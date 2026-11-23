/-
Split of the input leaf306_theorem6, Bordignon, Johnston and Starichkova Theorem 6,
along the proof the paper gives in Section 2.4, pages 10 to 16.
Source: arXiv 2207.09452v6, papers/P0009.pdf. The paper proves Theorem 6 as
Nathanson's Theorem 9.7, reference 40 of the paper, with the constants of Lemma 14.
Pieces:
* Rosser weights with beta = 2, Nathanson Theorem 9.3, as summed in BJS display 28;
* the sieve inequalities and the support bound of those weights, Nathanson Theorem 9.3;
* the identities G(z, lambda plus or minus) = V(z) plus or minus the sum of T_n,
  Nathanson Lemma 9.3, as used in the proof of BJS Proposition 13, page 14;
* the bounds for the sums of T_n, BJS Lemma 11, displays 13 and 14, Lemma 14 and Table 1;
* the constant K of BJS displays 29 and 30 from the strict hypothesis 4;
* the reduction from weights to displays 5 and 6 with the set Q, Nathanson Theorem 9.7.
The assembly theorem6_of_leaves306 is proved from these pieces.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ChenExplicit.LinearSieve

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

open Classical in
/-- The Rosser weights with beta = 2 of Nathanson Theorem 9.3, the weights lambda plus and
lambda minus of BJS Proposition 13, page 14, with the truncation of BJS display 28.
For squarefree d with prime factors p_1 > ... > p_r, the index of p_m is m, the number of
prime factors at least p_m, and p_m < y_m, y_m = (D / (p_1 ... p_m)) ^ (1 / 2), reads
p_1 ... p_(m-1) p_m ^ 3 < D. The weight is mu d when this holds for every index m of the
parity of j, and 0 otherwise; j = 1 gives lambda plus, j = 0 gives lambda minus. -/
def rosserWeight306 (D : ℝ) (j : ℕ) (d : ℕ) : ℝ :=
  if Squarefree d ∧ ∀ p ∈ d.primeFactors,
      (d.primeFactors.filter (fun q => p ≤ q)).card % 2 = j % 2 →
        ((∏ q ∈ d.primeFactors.filter (fun q => p < q), q : ℕ) : ℝ) * (p : ℝ) ^ 3 < D
  then (ArithmeticFunction.moebius d : ℝ) else 0

open Classical in
/-- BJS display 28, T_n(D, z): the sum over d = p_1 ... p_n dividing P(z), p_1 > ... > p_n,
with y_n ≤ p_n, that is D ≤ d p_n ^ 2, and p_m < y_m for every m < n with m ≡ n mod 2,
of g(d) V(p_n). Here p_n is the least prime factor of d and V(u) is the product of
1 - g(p) over the primes p of P below u, BJS display 11. -/
def rosserT306 (P : Set ℕ) (g : ArithmeticFunction ℝ) (z D : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p).divisors.filter (fun d : ℕ =>
      d.primeFactors.card = n ∧ D ≤ (d : ℝ) * (d.minFac : ℝ) ^ 2 ∧
      ∀ p ∈ d.primeFactors, (d.primeFactors.filter (fun q => p ≤ q)).card < n →
        (d.primeFactors.filter (fun q => p ≤ q)).card % 2 = n % 2 →
          ((∏ q ∈ d.primeFactors.filter (fun q => p < q), q : ℕ) : ℝ) * (p : ℝ) ^ 3 < D),
    g d * ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P (d.minFac : ℝ), (1 - g p)

/-- The Rosser weights are mu d or 0, so they lie in [-1, 1]. Nathanson Theorem 9.3. -/
theorem rosserWeight306_abs_le (D : ℝ) (j d : ℕ) : |rosserWeight306 D j d| ≤ 1 := by
  unfold rosserWeight306
  split_ifs
  · rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> simp [h]
  · simp

/-- LEAF: Nathanson Theorem 9.3, the sieve property of the Rosser weights used by BJS
Proposition 13, page 14: for squarefree m, the sum of lambda plus over the divisors of m is
at least the indicator of m = 1, and the sum of lambda minus is at most it.
Class MEDIUM: finite combinatorics, the Buchstab iteration over the least failing index. -/
theorem leaf306_rosser_sieve (D : ℝ) (m : ℕ) (hm : Squarefree m) :
    (if m = 1 then (1 : ℝ) else 0) ≤ ∑ d ∈ m.divisors, rosserWeight306 D 1 d ∧
      ∑ d ∈ m.divisors, rosserWeight306 D 0 d ≤ (if m = 1 then (1 : ℝ) else 0) := by
  sorry

/-- Nathanson Theorem 9.3, the level of the Rosser weights, as used in BJS display 10:
a nonzero weight at d with all prime factors below z ≤ D has d < D.
PROVED in burst-20261122 S61. For lambda plus apply the condition at the last odd index, for lambda minus at
the last even index, or use p_1 < z ≤ D when d is a single prime. -/
theorem leaf306_rosser_support (D z : ℝ) (hz : 1 < z) (hzD : z ≤ D) (j d : ℕ)
    (hd : ∀ p ∈ d.primeFactors, (p : ℝ) < z) (hw : rosserWeight306 D j d ≠ 0) :
    (d : ℝ) < D := by
  classical
  unfold rosserWeight306 at hw
  split_ifs at hw with hc
  · obtain ⟨hsq, hcond⟩ := hc
    have hprod : ∏ q ∈ d.primeFactors, q = d := Nat.prod_primeFactors_of_squarefree hsq
    have hD1 : 1 < D := by linarith
    rcases d.primeFactors.eq_empty_or_nonempty with hE | hne
    · rw [hE, prod_empty] at hprod
      rw [← hprod]; simpa using hD1
    set S := d.primeFactors with hS
    set p := S.min' hne with hpdef
    have hpS : p ∈ S := min'_mem _ _
    have hfle : S.filter (fun q => p ≤ q) = S :=
      filter_true_of_mem (fun q hq => min'_le _ _ hq)
    have hflt : S.filter (fun q => p < q) = S.erase p := by
      ext q; simp only [mem_filter, mem_erase]; constructor
      · rintro ⟨hq, hlt⟩; exact ⟨hlt.ne', hq⟩
      · rintro ⟨hne', hq⟩; exact ⟨hq, lt_of_le_of_ne (min'_le _ _ hq) (Ne.symm hne')⟩
    have hdp : d = p * ∏ q ∈ S.erase p, q :=
      hprod.symm.trans (mul_prod_erase S (fun x => x) hpS).symm
    have hp1 : (1:ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hpS).one_lt.le
    by_cases hpar : S.card % 2 = j % 2
    · have h := hcond p hpS (by rw [hfle]; exact hpar)
      rw [hflt] at h
      have hA : (0:ℝ) ≤ ((∏ q ∈ S.erase p, q : ℕ) : ℝ) := by positivity
      have : (d:ℝ) = (p:ℝ) * ((∏ q ∈ S.erase p, q : ℕ) : ℝ) := by
        rw [hdp]; push_cast; ring
      rw [this]
      have h2 : (0:ℝ) ≤ (p:ℝ)^2 - 1 := by nlinarith
      nlinarith [mul_nonneg (mul_nonneg hA (by linarith : (0:ℝ) ≤ p)) h2]
    · rcases (S.erase p).eq_empty_or_nonempty with hE2 | hne2
      · rw [hE2, prod_empty, mul_one] at hdp
        have := hd p hpS
        rw [hdp]; linarith
      · set q := (S.erase p).min' hne2 with hqdef
        have hqS' : q ∈ S.erase p := min'_mem _ _
        have hqS : q ∈ S := mem_of_mem_erase hqS'
        have hpq : p < q := lt_of_le_of_ne (min'_le _ _ hqS) (Ne.symm (ne_of_mem_erase hqS'))
        have hfle2 : S.filter (fun x => q ≤ x) = S.erase p := by
          ext x; simp only [mem_filter, mem_erase]; constructor
          · rintro ⟨hx, hle⟩; exact ⟨by rintro rfl; omega, hx⟩
          · rintro ⟨hxp, hx⟩; exact ⟨hx, min'_le _ _ (mem_erase.mpr ⟨hxp, hx⟩)⟩
        have hflt2 : S.filter (fun x => q < x) = (S.erase p).erase q := by
          ext x; simp only [mem_filter, mem_erase]; constructor
          · rintro ⟨hx, hlt⟩; exact ⟨hlt.ne', by rintro rfl; omega, hx⟩
          · rintro ⟨hxq, hxp, hx⟩
            exact ⟨hx, lt_of_le_of_ne (min'_le _ _ (mem_erase.mpr ⟨hxp, hx⟩)) (Ne.symm hxq)⟩
        have hcard : 1 ≤ S.card := card_pos.mpr hne
        have h := hcond q hqS (by rw [hfle2, card_erase_of_mem hpS]; omega)
        rw [hflt2] at h
        have hB : (0:ℝ) ≤ ((∏ x ∈ (S.erase p).erase q, x : ℕ) : ℝ) := by positivity
        have hA : ∏ x ∈ S.erase p, x = q * ∏ x ∈ (S.erase p).erase q, x :=
          (mul_prod_erase _ _ hqS').symm
        have : (d:ℝ) = (p:ℝ) * (q:ℝ) * ((∏ x ∈ (S.erase p).erase q, x : ℕ) : ℝ) := by
          rw [hdp, hA]; push_cast; ring
        rw [this]
        have hpq' : (p:ℝ) < q := by exact_mod_cast hpq
        have hq1 : (1:ℝ) ≤ q := by linarith
        have h1 : (p:ℝ) * q ≤ q ^ 3 := by
          nlinarith [mul_le_mul_of_nonneg_right hpq'.le (by linarith : (0:ℝ) ≤ q),
            mul_nonneg (sq_nonneg (q:ℝ)) (by linarith : (0:ℝ) ≤ q - 1)]
        nlinarith [mul_le_mul_of_nonneg_right h1 hB]
  · exact absurd rfl hw

/-- LEAF: Nathanson Lemma 9.3, as used in the proof of BJS Proposition 13, page 14:
G(z, lambda plus) = V(z) + the sum of T_n(D, z) over odd n.
Class MEDIUM: finite combinatorics, telescoping V(p) g(p) = V(p) - V(p') over the primes of P. -/
theorem leaf306_rosser_identity_upper (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (z D : ℝ) :
    ∑ d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p).divisors,
        rosserWeight306 D 1 d * g d =
      ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p) +
        ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd,
          rosserT306 P g z D n := by
  sorry

/-- LEAF: Nathanson Lemma 9.3, as used in the proof of BJS Proposition 13, page 14:
G(z, lambda minus) = V(z) - the sum of T_n(D, z) over even n.
Class MEDIUM: the same finite combinatorics as the upper identity. -/
theorem leaf306_rosser_identity_lower (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (z D : ℝ) :
    ∑ d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p).divisors,
        rosserWeight306 D 0 d * g d =
      ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p) -
        ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even,
          rosserT306 P g z D n := by
  sorry

/-- The functions f_n of BJS displays 15 to 17, Nathanson Chapter 9:
s f_1(s) = 3 - s for s ≤ 3 and 0 for s > 3; for n ≥ 2,
s f_n(s) = the integral over t > s of f_(n-1)(t - 1), display 16, except that for odd n and
s ≤ 3, s f_n(s) = 3 f_n(3) = the integral over t > 3 of f_(n-1)(t - 1), display 17.
The paper uses f_n only for s ≥ 1, n odd, and s ≥ 2, n even; other values are not used.
f_0 is set to 0 and is not used. -/
def bjsF306 : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => fun s => if s ≤ 3 then (3 - s) / s else 0
  | (n + 2) => fun s =>
      if Odd (n + 2) ∧ s ≤ 3 then (∫ t in Set.Ioi (3 : ℝ), bjsF306 (n + 1) (t - 1)) / s
      else (∫ t in Set.Ioi s, bjsF306 (n + 1) (t - 1)) / s

/-- The values c_n of BJS Table 2, page 7, for 2 ≤ n ≤ 500, with c_1 = 1 as stated after
display 18, and c_n = 0.9607 of Lemma 8 for n > 500. c_0 is set to 1 and is not used. -/
def bjsC306 (n : ℕ) : ℝ :=
  if n ≤ 1 then 1 else if n = 2 then 0.33 else if n = 3 then 0.39 else if n = 4 then 0.45
  else if n = 5 then 0.51 else if n = 6 then 0.54 else if n = 7 then 0.57
  else if n = 8 then 0.58 else if n ≤ 10 then 0.61 else if n ≤ 12 then 0.63
  else if n = 13 then 0.64 else if n = 14 then 0.65 else if n ≤ 18 then 0.66
  else if n ≤ 20 then 0.67 else if n ≤ 26 then 0.68 else if n ≤ 34 then 0.69
  else if n ≤ 46 then 0.7 else if n ≤ 82 then 0.71 else if n ≤ 345 then 0.72
  else if n ≤ 500 then 0.73 else 0.9607

/-- The quantity ξ_(s0) of BJS Lemma 11, page 11, for given γ_(s0), κ_(s0), ε,
cp = c_(n-1) ^ (n-2), cc = c_n ^ (n-1) and t = τ_(n-1). -/
def bjsXi306 (γ κ ε cp cc t : ℝ) : ℝ :=
  κ + (γ + κ) * ε + 2 * γ * cp / t + 2 * cc / t

/-- τ_n of BJS display 31, page 11, for a sequence c: τ_1 = 3; for even n ≥ 2,
τ_n = τ_(n-1) max of ξ_2, ξ_2.2, ξ_2.4, ξ_2.6, ξ_2.8, ξ_3; for odd n ≥ 3,
τ_n = τ_(n-1) max of ξ_3 and ξ tilde. γ_(s0) = e ^ (s0 - 2) for s0 ≤ 2.8 and γ_3 = 4 e / 3
by Lemma 9, page 8; κ_2 = 0.9607, κ_2.2 = 0.9557, κ_2.4 = 0.9457, κ_2.6 = 0.9261,
κ_2.8 = 0.8914, κ_3 = 0.8349 and κ tilde = 0.9214 by Lemma 10, pages 8 and 9.
τ_0 is set to 0 and is not used. -/
def bjsTau306 (c : ℕ → ℝ) (ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 3
  | (n + 2) =>
      let t := bjsTau306 c ε (n + 1)
      let cp := c (n + 1) ^ n
      let cc := c (n + 2) ^ (n + 1)
      if Even (n + 2) then
        t * max (max (max (bjsXi306 1 0.9607 ε cp cc t) (bjsXi306 (exp 0.2) 0.9557 ε cp cc t))
          (max (bjsXi306 (exp 0.4) 0.9457 ε cp cc t) (bjsXi306 (exp 0.6) 0.9261 ε cp cc t)))
          (max (bjsXi306 (exp 0.8) 0.8914 ε cp cc t) (bjsXi306 (4 * exp 1 / 3) 0.8349 ε cp cc t))
      else
        t * max (bjsXi306 (4 * exp 1 / 3) 0.8349 ε cp cc t)
          (0.9214 + (5 + 4 * ε) * ε + 6 * (1 + ε) * cp / t + 2 * (2 + ε) * cc / t)

/-- LEAF: the functions f_n are nonnegative where the paper uses them, BJS displays 15 to 17:
n odd with s ≥ 1, or n even with s ≥ 2.
Class EASY: induction on n with setIntegral_nonneg; the integrand is evaluated at t - 1 ≥ 1
for odd n - 1 and at t - 1 ≥ 2 for even n - 1. -/
theorem leaf306_fn_nonneg (n : ℕ) (s : ℝ) (hs : (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s)) :
    0 ≤ bjsF306 n s := by
  sorry

/-- LEAF: BJS display 13, Nathanson Theorem 9.4: for s ≥ 1, F(s) = 1 + the sum of f_n(s)
over odd n, for the solution F, f of display 8.
Class HARD: the delay differential equations against the integral recursion 15 to 17. -/
theorem leaf306_display13 (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (s : ℝ) (hs : 1 ≤ s) :
    HasSum (fun n : ℕ => if Odd n then bjsF306 n s else 0) (F s - 1) := by
  sorry

/-- LEAF: BJS display 14, Nathanson Theorem 9.4: for s ≥ 2, f(s) = 1 - the sum of f_n(s)
over even n ≥ 2, for the solution F, f of display 8. The term n = 0 is f_0 = 0.
Class HARD: as display 13. -/
theorem leaf306_display14 (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (s : ℝ) (hs : 2 ≤ s) :
    HasSum (fun n : ℕ => if Even n then bjsF306 n s else 0) (1 - f s) := by
  sorry

/-- LEAF: BJS Lemmas 7 and 8, pages 6 and 7: display 18,
f_n(s) ≤ 2 e ^ 2 c_n ^ (n - 1) h(s) for n odd and s ≥ 1 or n even and s ≥ 2,
with c_n of Table 2 for n ≤ 500, c_1 = 1, and c_n = 0.9607 beyond, Nathanson Lemma 9.7.
Class HARD: Lemma 7 is a Riemann sum computation, Lemma 8 is Nathanson's analytic bound. -/
theorem leaf306_display18 (n : ℕ) (hn : 1 ≤ n) (s : ℝ)
    (hs : (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s)) :
    bjsF306 n s ≤ 2 * exp 2 * bjsC306 n ^ (n - 1) * LeanLab.ChenExplicit.hSieve s := by
  sorry

/-- LEAF: BJS Lemma 11, pages 10 to 13: under displays 29 and 30 with 1 < K < 1 + ε and
any positive c_n satisfying display 18, T_n(D, z) ≤ V(z) (f_n(s) + ε τ_n e ^ 2 h(s)) for
n ≥ 1, with s ≥ 1 for odd n and s ≥ 2 for even n. The paper's strict inequality is weakened.
Class HARD: induction on n through Nathanson Lemma 9.8 with Lemmas 9 and 10. -/
theorem leaf306_lemma11 (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (ε : ℝ) (hε : 0 < ε) (K : ℝ) (hK1 : 1 < K) (hKε : K < 1 + ε)
    (h29 : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ ≤ K * (log z / log u))
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (h18 : ∀ n : ℕ, 1 ≤ n → ∀ s : ℝ, (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s) →
      bjsF306 n s ≤ 2 * exp 2 * c n ^ (n - 1) * LeanLab.ChenExplicit.hSieve s)
    (n : ℕ) (hn : 1 ≤ n) (D : ℝ)
    (hs : (Odd n ∧ 1 ≤ log D / log z) ∨ (Even n ∧ 2 ≤ log D / log z)) :
    rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (bjsF306 n (log D / log z) +
          ε * bjsTau306 c ε n * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := by
  sorry

/-- LEAF: BJS Lemmas 12 and 14 with Table 1, pages 13 to 16: for a row k, C_1, C_2 of
Table 1 and 0 < ε ≤ 1 / k, every partial sum of τ_n over odd n is at most C_1 and every
partial sum over even n is at most C_2, with c_n of Table 2. These are the bounds
C_1(ε) = the sum of τ_(2n-1) ≤ C_1 and C_2(ε) = the sum of τ_(2n) ≤ C_2 of displays 43, 44.
Class HARD: the τ_n for n ≤ 500, τ' of display 40 for n ≤ 501, the geometric tail with J. -/
theorem leaf306_lemma14_table (k C₁ C₂ : ℕ) (hrow : (k, C₁, C₂) ∈ LeanLab.ChenExplicit.table1)
    (ε : ℝ) (hε : 0 < ε) (hεk : ε ≤ 1 / (k : ℝ)) (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 ε n ≤ C₁ ∧
      ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 ε n ≤ C₂ := by
  sorry

/-- h(s) of display 7 is nonnegative for s ≥ 0. -/
theorem hSieve_nonneg306 (s : ℝ) (hs : 0 ≤ s) : 0 ≤ LeanLab.ChenExplicit.hSieve s := by
  unfold LeanLab.ChenExplicit.hSieve
  split_ifs
  · exact (exp_pos _).le
  · exact (exp_pos _).le
  · exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hs)) (exp_pos _).le

/-- V(z) is nonnegative when 0 ≤ g(p) < 1 on P. -/
theorem V_nonneg306 (P : Set ℕ) (z : ℝ) (g : ArithmeticFunction ℝ)
    (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) :
    0 ≤ ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p) := by
  classical
  refine Finset.prod_nonneg fun p hp => ?_
  simp only [LeanLab.ChenExplicit.primesBelowIn, Finset.mem_filter] at hp
  linarith [(hgp p hp.2).2]

/-- The values c_n of Table 2 are positive. -/
theorem bjsC306_pos (n : ℕ) : 0 < bjsC306 n := by
  unfold bjsC306
  positivity

/-- BJS Lemma 11 summed over odd n with display 13, then Lemma 14 and Table 1,
pages 10 to 16, the upper half of Proposition 13: under displays 29 and 30 with s ≥ 1,
the sum of T_n(D, z) over odd n is at most V(z) (F(s) - 1 + ε C_1 e ^ 2 h(s)).
Table 1 is read for every ε ≤ 1 / k, as LinearSieve.lean records.
Proved in burst-20261122 S61 from leaf306_lemma11, leaf306_display13, leaf306_display18,
leaf306_fn_nonneg and leaf306_lemma14_table. -/
theorem leaf306_T_odd_bound (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (k C₁ C₂ : ℕ) (hrow : (k, C₁, C₂) ∈ LeanLab.ChenExplicit.table1)
    (ε : ℝ) (hε : 0 < ε) (hεk : ε ≤ 1 / (k : ℝ))
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (K : ℝ) (hK1 : 1 < K) (hKε : K < 1 + ε)
    (h29 : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ ≤ K * (log z / log u))
    (D : ℝ) (hD : z ≤ D) :
    ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd,
        rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (F (log D / log z) - 1 +
          ε * C₁ * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := by
  classical
  set s := log D / log z with hsdef
  have hlogz : 0 < log z := log_pos (by linarith)
  have hs1 : 1 ≤ s := by
    rw [hsdef, le_div_iff₀ hlogz, one_mul]; exact log_le_log (by linarith) hD
  have hV0 := V_nonneg306 P z g hgp
  have hh0 : 0 ≤ LeanLab.ChenExplicit.hSieve s := hSieve_nonneg306 s (by linarith)
  have hcpos : ∀ n, 0 < bjsC306 n := bjsC306_pos
  have hT : ∀ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd, rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (bjsF306 n s + ε * bjsTau306 bjsC306 ε n * exp 2 * LeanLab.ChenExplicit.hSieve s) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    exact leaf306_lemma11 P hP z hz g hg hgp ε hε K hK1 hKε h29 bjsC306 hcpos
      (fun m hm s' hs' => leaf306_display18 m hm s' hs') n hn.1.1 D (Or.inl ⟨hn.2, hs1⟩)
  have hf : ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd, bjsF306 n s ≤ F s - 1 := by
    rw [Finset.sum_filter]
    refine sum_le_hasSum _ (fun n _ => ?_) (leaf306_display13 F f hF s hs1)
    split_ifs with ho
    · exact leaf306_fn_nonneg n s (Or.inl ⟨ho, hs1⟩)
    · exact le_refl 0
  have hτ := (leaf306_lemma14_table k C₁ C₂ hrow ε hε hεk
    (LeanLab.ChenExplicit.primesBelowIn P z).card).1
  have hco : 0 ≤ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ε * exp 2 *
      LeanLab.ChenExplicit.hSieve s :=
    mul_nonneg (mul_nonneg (mul_nonneg hV0 hε.le) (exp_pos _).le) hh0
  calc _ ≤ ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd, (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (bjsF306 n s + ε * bjsTau306 bjsC306 ε n * exp 2 * LeanLab.ChenExplicit.hSieve s) :=
        Finset.sum_le_sum hT
    _ = (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd, bjsF306 n s +
        ((∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ε * exp 2 *
          LeanLab.ChenExplicit.hSieve s) * ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd, bjsTau306 bjsC306 ε n := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun n _ => by ring)
    _ ≤ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * (F s - 1) +
        ((∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ε * exp 2 *
          LeanLab.ChenExplicit.hSieve s) * (C₁ : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hf hV0) (mul_le_mul_of_nonneg_left hτ hco)
    _ = _ := by ring

/-- BJS Lemma 11 summed over even n with display 14, then Lemma 14 and Table 1,
pages 10 to 16, the lower half of Proposition 13: under displays 29 and 30 with s ≥ 2,
the sum of T_n(D, z) over even n is at most V(z) (1 - f(s) + ε C_2 e ^ 2 h(s)).
Proved in burst-20261122 S61 from the same pieces with leaf306_display14. -/
theorem leaf306_T_even_bound (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (k C₁ C₂ : ℕ) (hrow : (k, C₁, C₂) ∈ LeanLab.ChenExplicit.table1)
    (ε : ℝ) (hε : 0 < ε) (hεk : ε ≤ 1 / (k : ℝ))
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (K : ℝ) (hK1 : 1 < K) (hKε : K < 1 + ε)
    (h29 : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ ≤ K * (log z / log u))
    (D : ℝ) (hD : z ^ 2 ≤ D) :
    ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even,
        rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (1 - f (log D / log z) +
          ε * C₂ * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := by
  classical
  set s := log D / log z with hsdef
  have hlogz : 0 < log z := log_pos (by linarith)
  have hs1 : 2 ≤ s := by
    rw [hsdef, le_div_iff₀ hlogz]
    have h2 : log (z ^ 2) ≤ log D := log_le_log (by positivity) hD
    rw [Real.log_pow] at h2; push_cast at h2; linarith
  have hV0 := V_nonneg306 P z g hgp
  have hh0 : 0 ≤ LeanLab.ChenExplicit.hSieve s := hSieve_nonneg306 s (by linarith)
  have hcpos : ∀ n, 0 < bjsC306 n := bjsC306_pos
  have hT : ∀ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even, rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (bjsF306 n s + ε * bjsTau306 bjsC306 ε n * exp 2 * LeanLab.ChenExplicit.hSieve s) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    exact leaf306_lemma11 P hP z hz g hg hgp ε hε K hK1 hKε h29 bjsC306 hcpos
      (fun m hm s' hs' => leaf306_display18 m hm s' hs') n hn.1.1 D (Or.inr ⟨hn.2, hs1⟩)
  have hf : ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even, bjsF306 n s ≤ 1 - f s := by
    rw [Finset.sum_filter]
    refine sum_le_hasSum _ (fun n _ => ?_) (leaf306_display14 F f hF s hs1)
    split_ifs with ho
    · exact leaf306_fn_nonneg n s (Or.inr ⟨ho, hs1⟩)
    · exact le_refl 0
  have hτ := (leaf306_lemma14_table k C₁ C₂ hrow ε hε hεk
    (LeanLab.ChenExplicit.primesBelowIn P z).card).2
  have hco : 0 ≤ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ε * exp 2 *
      LeanLab.ChenExplicit.hSieve s :=
    mul_nonneg (mul_nonneg (mul_nonneg hV0 hε.le) (exp_pos _).le) hh0
  calc _ ≤ ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even, (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (bjsF306 n s + ε * bjsTau306 bjsC306 ε n * exp 2 * LeanLab.ChenExplicit.hSieve s) :=
        Finset.sum_le_sum hT
    _ = (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even, bjsF306 n s +
        ((∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ε * exp 2 *
          LeanLab.ChenExplicit.hSieve s) * ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even, bjsTau306 bjsC306 ε n := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun n _ => by ring)
    _ ≤ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * (1 - f s) +
        ((∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ε * exp 2 *
          LeanLab.ChenExplicit.hSieve s) * (C₂ : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hf hV0) (mul_le_mul_of_nonneg_left hτ hco)
    _ = _ := by ring

/-- The constant K of BJS displays 29 and 30 from the strict display 4. With finitely
many primes below z, the ratio of the product to log z / log u has supremum below 1 + ε,
so one K with 1 < K < 1 + ε serves every u. The paper uses this step silently when it
applies Lemma 11 in the proof of Theorem 6, page 16.
PROVED in burst-20261122 S61: the product is a step function of u, constant between consecutive primes. -/
theorem leaf306_uniform_K (P : Set ℕ) (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) (ε : ℝ) (hε : 0 < ε)
    (h4 : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ < (1 + ε) * (log z / log u)) :
    ∃ K : ℝ, 1 < K ∧ K < 1 + ε ∧ ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ ≤ K * (log z / log u) := by
  classical
  set S := LeanLab.ChenExplicit.primesBelowIn P z with hS
  have hmemS : ∀ p ∈ S, p ∈ P ∧ (p : ℝ) < z := by
    intro p hp
    simp only [hS, LeanLab.ChenExplicit.primesBelowIn, Finset.mem_filter, Finset.mem_range,
      Nat.lt_ceil] at hp
    exact ⟨hp.2, hp.1⟩
  set Pr : ℝ → ℝ := fun u => ∏ p ∈ S.filter (fun p : ℕ => u ≤ (p : ℝ)), (1 - g p)⁻¹ with hPr
  have hlogz : 0 < log z := Real.log_pos (by linarith)
  set T := S.filter (fun p : ℕ => 1 < (p : ℝ)) with hT
  set a : ℕ → ℝ := fun p => Pr p * log p / log z with ha
  set M := T.fold max 1 a with hM
  have hM1 : 1 ≤ M := by
    rw [hM, Finset.le_fold_max]; left; exact le_refl _
  have hMlt : M < 1 + ε := by
    rw [hM, Finset.fold_max_lt]
    refine ⟨by linarith, ?_⟩
    intro p hp
    rw [hT, Finset.mem_filter] at hp
    have hp1 := hp.2
    have hpz := (hmemS p hp.1).2
    have h := h4 p hp1 hpz
    have hlp : 0 < log (p : ℝ) := Real.log_pos hp1
    show Pr p * log p / log z < 1 + ε
    rw [div_lt_iff₀ hlogz]
    have := mul_lt_mul_of_pos_right h hlp
    calc Pr p * log p < (1 + ε) * (log z / log p) * log p := this
      _ = (1 + ε) * log z := by field_simp
  refine ⟨(M + 1 + ε) / 2, by linarith, by linarith, ?_⟩
  intro u hu1 huz
  have hlu : 0 < log u := Real.log_pos hu1
  have hluz : log u < log z := Real.log_lt_log (by linarith) huz
  have hratio : 1 < log z / log u := by rw [one_lt_div hlu]; exact hluz
  show Pr u ≤ _
  by_cases hF : (S.filter (fun p : ℕ => u ≤ (p : ℝ))).Nonempty
  · set p0 := (S.filter (fun p : ℕ => u ≤ (p : ℝ))).min' hF with hp0
    have hp0mem := Finset.min'_mem _ hF
    rw [← hp0, Finset.mem_filter] at hp0mem
    have hfeq : S.filter (fun p : ℕ => u ≤ (p : ℝ)) = S.filter (fun p : ℕ => (p0 : ℝ) ≤ (p : ℝ)) := by
      ext p
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have : p0 ≤ p := Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨h1, h2⟩)
        exact_mod_cast this
      · rintro ⟨h1, h2⟩
        exact ⟨h1, le_trans hp0mem.2 h2⟩
    have hPreq : Pr u = Pr p0 := by
      simp only [hPr]; rw [hfeq]
    have hp01 : 1 < (p0 : ℝ) := lt_of_lt_of_le hu1 hp0mem.2
    have hp0T : p0 ∈ T := by rw [hT, Finset.mem_filter]; exact ⟨hp0mem.1, hp01⟩
    have hap0 : a p0 ≤ M := by
      rw [hM, Finset.le_fold_max]; right; exact ⟨p0, hp0T, le_refl _⟩
    have hlp0 : 0 < log (p0 : ℝ) := Real.log_pos hp01
    have hlup : log u ≤ log (p0 : ℝ) := Real.log_le_log (by linarith) hp0mem.2
    have hPr0 : Pr p0 ≤ M * (log z / log p0) := by
      have : Pr p0 * log p0 / log z ≤ M := hap0
      rw [div_le_iff₀ hlogz] at this
      rw [mul_div_assoc', le_div_iff₀ hlp0]
      linarith
    have h2 : log z / log p0 ≤ log z / log u :=
      div_le_div_of_nonneg_left hlogz.le hlu hlup
    rw [hPreq]
    calc Pr p0 ≤ M * (log z / log p0) := hPr0
      _ ≤ M * (log z / log u) := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ ≤ (M + 1 + ε) / 2 * (log z / log u) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hF
    have : Pr u = 1 := by simp only [hPr]; rw [hF, Finset.prod_empty]
    rw [this]
    have hK1 : 1 < (M + 1 + ε) / 2 := by linarith
    nlinarith

open Classical in
/-- LEAF: Nathanson Theorem 9.7, upper half, the step the proof of BJS Theorem 6 on page 16
takes over unchanged, with the set Q of display 4 and the level Q D of display 10.
Sieve n coprime to the primes of Q below z by Mobius inversion and the primes of P \ Q by
weights lam with |lam| ≤ 1, level D and the upper sieve property, whose main terms
G_n(lam) are at most c V_n(z) for P \ Q. Then S(A, P, z) ≤ c X_A + R.
Class MEDIUM: interchange of finite sums and the injection (d, e) to d e into d < Q D. -/
theorem leaf306_reduction_upper (supp : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ℕ → ArithmeticFunction ℝ) (hg : ∀ n, (g n).IsMultiplicative)
    (hgp : ∀ n, ∀ p ∈ P, 0 ≤ g n p ∧ g n p < 1)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q ∈ P) (D : ℝ) (hD : 0 < D)
    (lam : ℕ → ℝ) (c : ℝ) (hlam : ∀ d, |lam d| ≤ 1)
    (hsupp : ∀ d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn {p | p ∈ P ∧ p ∉ Q} z,
      p).divisors, lam d ≠ 0 → (d : ℝ) < D)
    (hsieve : ∀ m ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn {p | p ∈ P ∧ p ∉ Q} z,
      p).divisors, (if m = 1 then (1 : ℝ) else 0) ≤ ∑ d ∈ m.divisors, lam d)
    (hmain : ∀ n, ∑ d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn
        {p | p ∈ P ∧ p ∉ Q} z, p).divisors, lam d * g n d ≤
      c * ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn {p | p ∈ P ∧ p ∉ Q} z, (1 - g n p)) :
    let PP : ℕ := ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p
    let S : ℝ := ∑ n ∈ supp, if Nat.Coprime n PP then a n else 0
    let XA : ℝ := ∑ n ∈ supp, a n * ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g n p)
    let r : ℕ → ℝ := fun d =>
      (∑ n ∈ supp, if d ∣ n then a n else 0) - ∑ n ∈ supp, a n * g n d
    let R : ℝ := ∑ d ∈ PP.divisors.filter
      (fun d : ℕ => (d : ℝ) < (∏ q ∈ Q, (q : ℝ)) * D), |r d|
    S ≤ c * XA + R := by
  sorry

open Classical in
/-- LEAF: Nathanson Theorem 9.7, lower half, as in the upper half with the lower sieve
property and main terms G_n(lam) at least c V_n(z) for P \ Q. Then c X_A - R ≤ S(A, P, z).
Class MEDIUM: the same interchange of sums as the upper half. -/
theorem leaf306_reduction_lower (supp : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ℕ → ArithmeticFunction ℝ) (hg : ∀ n, (g n).IsMultiplicative)
    (hgp : ∀ n, ∀ p ∈ P, 0 ≤ g n p ∧ g n p < 1)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q ∈ P) (D : ℝ) (hD : 0 < D)
    (lam : ℕ → ℝ) (c : ℝ) (hlam : ∀ d, |lam d| ≤ 1)
    (hsupp : ∀ d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn {p | p ∈ P ∧ p ∉ Q} z,
      p).divisors, lam d ≠ 0 → (d : ℝ) < D)
    (hsieve : ∀ m ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn {p | p ∈ P ∧ p ∉ Q} z,
      p).divisors, ∑ d ∈ m.divisors, lam d ≤ (if m = 1 then (1 : ℝ) else 0))
    (hmain : ∀ n, c * ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn {p | p ∈ P ∧ p ∉ Q} z,
        (1 - g n p) ≤
      ∑ d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn
        {p | p ∈ P ∧ p ∉ Q} z, p).divisors, lam d * g n d) :
    let PP : ℕ := ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p
    let S : ℝ := ∑ n ∈ supp, if Nat.Coprime n PP then a n else 0
    let XA : ℝ := ∑ n ∈ supp, a n * ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g n p)
    let r : ℕ → ℝ := fun d =>
      (∑ n ∈ supp, if d ∣ n then a n else 0) - ∑ n ∈ supp, a n * g n d
    let R : ℝ := ∑ d ∈ PP.divisors.filter
      (fun d : ℕ => (d : ℝ) < (∏ q ∈ Q, (q : ℝ)) * D), |r d|
    c * XA - R ≤ S := by
  sorry

/-- Primes of P below z are prime and lie below z. Helper for the assembly. -/
theorem mem_primesBelowIn306 {P : Set ℕ} (hP : ∀ p ∈ P, p.Prime) {z : ℝ} {p : ℕ}
    (hp : p ∈ LeanLab.ChenExplicit.primesBelowIn P z) : p.Prime ∧ (p : ℝ) < z := by
  classical
  simp only [LeanLab.ChenExplicit.primesBelowIn, Finset.mem_filter, Finset.mem_range] at hp
  exact ⟨hP p hp.2, Nat.lt_ceil.mp hp.1⟩

/-- The product of the primes of P below z is squarefree. Helper for the assembly. -/
theorem squarefree_primesBelowIn306 {P : Set ℕ} (hP : ∀ p ∈ P, p.Prime) (z : ℝ) :
    Squarefree (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    fun p hp => (mem_primesBelowIn306 hP hp).1.squarefree
  simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (mem_primesBelowIn306 hP hp).1
    (mem_primesBelowIn306 hP hq).1).mpr hpq

/-- A prime factor of a divisor of the product of the primes of P below z lies below z.
Helper for the assembly. -/
theorem primeFactor_lt_of_dvd306 {P : Set ℕ} (hP : ∀ p ∈ P, p.Prime) {z : ℝ} {d : ℕ}
    (hd : d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p).divisors) :
    ∀ p ∈ d.primeFactors, (p : ℝ) < z := by
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hdvd := (Nat.dvd_of_mem_primeFactors hp).trans (Nat.mem_divisors.mp hd).1
  obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp hdvd
  have hr' := mem_primesBelowIn306 hP hr
  rw [(Nat.prime_dvd_prime_iff_eq hpp hr'.1).mp hpr]
  exact hr'.2

open Classical in
/-- BJS Theorem 6, the explicit linear sieve, assembled from the pieces of its proof in
Section 2.4: the Rosser weights for the primes of P \ Q, their sieve property and level,
the identities of Nathanson Lemma 9.3, the bounds of BJS Lemma 11, Proposition 13 and
Lemma 14 with Table 1, and the reduction of Nathanson Theorem 9.7.
No sorry occurs in this assembly; it is CONDITIONAL ON the LEAF theorems of this file. -/
theorem theorem6_of_leaves306 : LeanLab.ChenExplicit.Theorem6Stmt := by
  intro F f hF k C₁ C₂ hrow ε hε hεk supp a h0 ha hsuppa P hP z hz g hg hgp Q hQ h4 D
  let P' : Set ℕ := {p | p ∈ P ∧ p ∉ Q}
  have hP' : ∀ p ∈ P', p.Prime := fun p hp => hP p hp.1
  have hgp' : ∀ n, ∀ p ∈ P', 0 ≤ g n p ∧ g n p < 1 := fun n p hp => hgp n p hp.1
  have hfil : ∀ u : ℝ,
      (LeanLab.ChenExplicit.primesBelowIn P' z).filter (fun p : ℕ => u ≤ (p : ℝ)) =
        (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => p ∉ Q ∧ u ≤ (p : ℝ)) := by
    intro u
    ext p
    simp only [LeanLab.ChenExplicit.primesBelowIn, Finset.mem_filter, Finset.mem_range,
      Set.mem_ofPred_eq, P']
    tauto
  have hK : ∀ n, ∃ K : ℝ, 1 < K ∧ K < 1 + ε ∧ ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P' z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g n p)⁻¹ ≤ K * (log z / log u) := fun n =>
    leaf306_uniform_K P' z hz (g n) (hgp' n) ε hε
      (fun u hu1 hu2 => by rw [hfil]; exact h4 n u hu1 hu2)
  have hsqP' := squarefree_primesBelowIn306 hP' z
  intro PP s S XA r R
  refine ⟨fun hD => ?_, fun hD => ?_⟩
  · have hDpos : 0 < D := by linarith
    exact leaf306_reduction_upper supp a ha P hP z hz g hg hgp Q hQ D hDpos
      (rosserWeight306 D 1) (F s + ε * C₁ * exp 2 * LeanLab.ChenExplicit.hSieve s)
      (rosserWeight306_abs_le D 1)
      (fun d hd hw => leaf306_rosser_support D z (by linarith) hD 1 d
        (primeFactor_lt_of_dvd306 hP' hd) hw)
      (fun m hm => (leaf306_rosser_sieve D m
        (hsqP'.squarefree_of_dvd (Nat.mem_divisors.mp hm).1)).1)
      (fun n => by
        obtain ⟨K, hK1, hKε, h29⟩ := hK n
        rw [leaf306_rosser_identity_upper P' hP' (g n) (hg n) z D]
        have hT := leaf306_T_odd_bound F f hF k C₁ C₂ hrow ε hε hεk P' hP' z hz (g n) (hg n)
          (hgp' n) K hK1 hKε h29 D hD
        have he : (F s + ε * C₁ * exp 2 * LeanLab.ChenExplicit.hSieve s) *
            ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P' z, (1 - g n p) =
            ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P' z, (1 - g n p) +
              (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P' z, (1 - g n p)) *
                (F (log D / log z) - 1 +
                  ε * C₁ * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := by
          simp only [s]; ring
        rw [he]
        linarith)
  · have hDpos : 0 < D := by nlinarith
    have hzD : z ≤ D := by nlinarith
    exact leaf306_reduction_lower supp a ha P hP z hz g hg hgp Q hQ D hDpos
      (rosserWeight306 D 0) (f s - ε * C₂ * exp 2 * LeanLab.ChenExplicit.hSieve s)
      (rosserWeight306_abs_le D 0)
      (fun d hd hw => leaf306_rosser_support D z (by linarith) hzD 0 d
        (primeFactor_lt_of_dvd306 hP' hd) hw)
      (fun m hm => (leaf306_rosser_sieve D m
        (hsqP'.squarefree_of_dvd (Nat.mem_divisors.mp hm).1)).2)
      (fun n => by
        obtain ⟨K, hK1, hKε, h29⟩ := hK n
        rw [leaf306_rosser_identity_lower P' hP' (g n) (hg n) z D]
        have hT := leaf306_T_even_bound F f hF k C₁ C₂ hrow ε hε hεk P' hP' z hz (g n) (hg n)
          (hgp' n) K hK1 hKε h29 D hD
        have he : (f s - ε * C₂ * exp 2 * LeanLab.ChenExplicit.hSieve s) *
            ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P' z, (1 - g n p) =
            ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P' z, (1 - g n p) -
              (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P' z, (1 - g n p)) *
                (1 - f (log D / log z) +
                  ε * C₂ * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := by
          simp only [s]; ring
        rw [he]
        linarith)

#print axioms rosserWeight306_abs_le
#print axioms leaf306_rosser_support
#print axioms leaf306_uniform_K
#print axioms leaf306_T_odd_bound
#print axioms leaf306_T_even_bound
#print axioms hSieve_nonneg306
#print axioms V_nonneg306
#print axioms bjsC306_pos
#print axioms theorem6_of_leaves306

end LeanLab.Cai2002

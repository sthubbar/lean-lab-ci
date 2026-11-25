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

/-- The prime factors of a squarefree `d` split at a prime factor `p` of `d` into those below
`p`, `p` itself, and those above. -/
private theorem primeFactors_prod_split306 {d p : ℕ} (hsf : Squarefree d)
    (hp : p ∈ d.primeFactors) :
    (∏ q ∈ d.primeFactors.filter (fun q => q < p), q) * p *
        (∏ q ∈ d.primeFactors.filter (fun q => p < q), q) = d := by
  classical
  have hsplit := Finset.prod_filter_mul_prod_filter_not (d.primeFactors) (fun q => q < p)
    (fun q => q)
  have hins : d.primeFactors.filter (fun q => ¬ q < p) =
      insert p (d.primeFactors.filter (fun q => p < q)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_insert, not_lt]
    constructor
    · rintro ⟨hq, hqp⟩
      rcases lt_or_eq_of_le hqp with h | h
      · exact Or.inr ⟨hq, h⟩
      · exact Or.inl h.symm
    · rintro (rfl | ⟨hq, h⟩)
      · exact ⟨hp, le_rfl⟩
      · exact ⟨hq, le_of_lt h⟩
  have hnot : p ∉ d.primeFactors.filter (fun q => p < q) := by
    simp only [Finset.mem_filter]
    rintro ⟨-, h⟩
    exact absurd h (lt_irrefl p)
  calc (∏ q ∈ d.primeFactors.filter (fun q => q < p), q) * p *
        (∏ q ∈ d.primeFactors.filter (fun q => p < q), q)
      = (∏ q ∈ d.primeFactors.filter (fun q => q < p), q) *
        (∏ q ∈ d.primeFactors.filter (fun q => ¬ q < p), q) := by
        rw [hins, Finset.prod_insert hnot, mul_assoc]
    _ = ∏ q ∈ d.primeFactors, q := hsplit
    _ = d := Nat.prod_primeFactors_of_squarefree hsf

/-- A prime factor `p` of `d` with at least as few factors below it as `2` gives `d ≤ p ^ 3`
times the product of the factors above `p`. -/
private theorem primeFactors_prod_le_cube306 {d p : ℕ} (hsf : Squarefree d)
    (hp : p ∈ d.primeFactors)
    (hbelow : (∏ q ∈ d.primeFactors.filter (fun q => q < p), q) ≤ p ^ 2) :
    d ≤ p ^ 3 * (∏ q ∈ d.primeFactors.filter (fun q => p < q), q) := by
  have hsplit := primeFactors_prod_split306 hsf hp
  calc d = (∏ q ∈ d.primeFactors.filter (fun q => q < p), q) * p *
        (∏ q ∈ d.primeFactors.filter (fun q => p < q), q) := hsplit.symm
    _ ≤ p ^ 2 * p * (∏ q ∈ d.primeFactors.filter (fun q => p < q), q) := by
        refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hbelow)
    _ = p ^ 3 * (∏ q ∈ d.primeFactors.filter (fun q => p < q), q) := by ring

/-- The last step of the support bound: a prime factor `p` of `d` whose index has the parity of
`j`, with at most two prime factors of `d` below it, forces `d < D`. -/
private theorem index_case306 {D : ℝ} {j d : ℕ} (hsf : Squarefree d)
    (hcond : ∀ p ∈ d.primeFactors,
      (d.primeFactors.filter (fun q => p ≤ q)).card % 2 = j % 2 →
        ((∏ q ∈ d.primeFactors.filter (fun q => p < q), q : ℕ) : ℝ) * (p : ℝ) ^ 3 < D)
    {p : ℕ} (hp : p ∈ d.primeFactors)
    (hcpar : (d.primeFactors.filter (fun q => p ≤ q)).card % 2 = j % 2)
    (hbelow : (∏ q ∈ d.primeFactors.filter (fun q => q < p), q) ≤ p ^ 2) :
    (d : ℝ) < D := by
  have hb := hcond p hp hcpar
  have hle := primeFactors_prod_le_cube306 hsf hp hbelow
  have hcast : ((p ^ 3 * ∏ q ∈ d.primeFactors.filter (fun q => p < q), q : ℕ) : ℝ) =
      (p : ℝ) ^ 3 * ((∏ q ∈ d.primeFactors.filter (fun q => p < q), q : ℕ) : ℝ) := by
    push_cast
    ring
  have hler : (d : ℝ) ≤ (p : ℝ) ^ 3 *
      ((∏ q ∈ d.primeFactors.filter (fun q => p < q), q : ℕ) : ℝ) := by
    rw [← hcast]
    exact_mod_cast hle
  nlinarith [hler, hb]

/-- LEAF: Nathanson Theorem 9.3, the level of the Rosser weights, as used in BJS display 10:
a nonzero weight at d with all prime factors below z ≤ D has d < D.
Class EASY: for lambda plus apply the condition at the last odd index, for lambda minus at
the last even index, or use p_1 < z ≤ D when d is a single prime. -/
theorem leaf306_rosser_support (D z : ℝ) (hz : 1 < z) (hzD : z ≤ D) (j d : ℕ)
    (hd : ∀ p ∈ d.primeFactors, (p : ℝ) < z) (hw : rosserWeight306 D j d ≠ 0) :
    (d : ℝ) < D := by
  classical
  rw [rosserWeight306] at hw
  split_ifs at hw with hcon
  · obtain ⟨hsf, hcond⟩ := hcon
    have hdprod : ∏ q ∈ d.primeFactors, q = d := Nat.prod_primeFactors_of_squarefree hsf
    have hzD' : (1 : ℝ) < D := lt_of_lt_of_le hz hzD
    have hprime : ∀ p ∈ d.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
    rcases eq_or_ne d.primeFactors.card 0 with hn0 | hn0
    · have hAe : d.primeFactors = ∅ := Finset.card_eq_zero.mp hn0
      have hd1 : d = 1 := by rw [← hdprod, hAe, Finset.prod_empty]
      rw [hd1]
      push_cast
      linarith
    rcases eq_or_ne d.primeFactors.card 1 with hn1 | hn1
    · obtain ⟨p0, hp0⟩ := Finset.card_eq_one.mp hn1
      have hdp : d = p0 := by rw [← hdprod, hp0, Finset.prod_singleton]
      have hlt : (p0 : ℝ) < z := hd p0 (by rw [hp0]; exact Finset.mem_singleton_self p0)
      rw [hdp]
      linarith
    have hge2 : 2 ≤ d.primeFactors.card := by omega
    have hne : d.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p0, hp0mem, hp0le⟩ : ∃ p0 ∈ d.primeFactors, ∀ q ∈ d.primeFactors, p0 ≤ q :=
      ⟨_, Finset.min'_mem _ hne, fun q hq => Finset.min'_le _ q hq⟩
    have hp0prime : p0.Prime := hprime p0 hp0mem
    -- the two candidate indices: the least prime factor, or the second least
    by_cases hpar : d.primeFactors.card % 2 = j % 2
    · have hfil : d.primeFactors.filter (fun q => p0 ≤ q) = d.primeFactors := by
        ext q
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.1, fun h => ⟨h, hp0le q h⟩⟩
      have hcpar : (d.primeFactors.filter (fun q => p0 ≤ q)).card % 2 = j % 2 := by
        rw [hfil]; exact hpar
      refine index_case306 hsf hcond hp0mem hcpar ?_
      have hempty : d.primeFactors.filter (fun q => q < p0) = ∅ :=
        Finset.eq_empty_iff_forall_notMem.mpr (fun q hq => by
          rw [Finset.mem_filter] at hq
          exact absurd (hp0le q hq.1) (not_le.mpr hq.2))
      rw [hempty, Finset.prod_empty]
      have h2 : 2 ≤ p0 := hp0prime.two_le
      nlinarith
    · have hne2 : (d.primeFactors.erase p0).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hp0mem]
        omega
      obtain ⟨p1, hp1mem', hp1le'⟩ :
          ∃ p1 ∈ d.primeFactors.erase p0, ∀ q ∈ d.primeFactors.erase p0, p1 ≤ q :=
        ⟨_, Finset.min'_mem _ hne2, fun q hq => Finset.min'_le _ q hq⟩
      obtain ⟨hp1ne, hp1mem⟩ := Finset.mem_erase.mp hp1mem'
      have hp1le : ∀ q ∈ d.primeFactors, q ≠ p0 → p1 ≤ q :=
        fun q hq hnq => hp1le' q (Finset.mem_erase.mpr ⟨hnq, hq⟩)
      have hp0ltp1 : p0 < p1 := lt_of_le_of_ne (hp0le p1 hp1mem) hp1ne.symm
      have hfil : d.primeFactors.filter (fun q => p1 ≤ q) = d.primeFactors.erase p0 := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hq, hle⟩
          exact ⟨fun h => absurd (h ▸ hle) (not_le.mpr hp0ltp1), hq⟩
        · rintro ⟨hqne, hq⟩
          exact ⟨hq, hp1le q hq hqne⟩
      have hcpar : (d.primeFactors.filter (fun q => p1 ≤ q)).card % 2 = j % 2 := by
        rw [hfil, Finset.card_erase_of_mem hp0mem]
        omega
      refine index_case306 hsf hcond hp1mem hcpar ?_
      have hsub : d.primeFactors.filter (fun q => q < p1) = {p0} := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hq, hlt⟩
          by_contra hne
          exact absurd (hp1le q hq hne) (not_le.mpr hlt)
        · rintro rfl
          exact ⟨hp0mem, hp0ltp1⟩
      rw [hsub, Finset.prod_singleton]
      have h2 : 2 ≤ p1 := (hprime p1 hp1mem).two_le
      nlinarith

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

/-- LEAF: BJS Lemma 11 summed over odd n with display 13, then Lemma 14 and Table 1,
pages 10 to 16, the upper half of Proposition 13: under displays 29 and 30 with s ≥ 1,
the sum of T_n(D, z) over odd n is at most V(z) (F(s) - 1 + ε C_1 e ^ 2 h(s)).
Table 1 is read for every ε ≤ 1 / k, as LinearSieve.lean records.
Class HARD: Lemmas 7 to 12 and 14 with their numerics, and Nathanson Theorem 9.4. -/
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
  sorry

/-- LEAF: BJS Lemma 11 summed over even n with display 14, then Lemma 14 and Table 1,
pages 10 to 16, the lower half of Proposition 13: under displays 29 and 30 with s ≥ 2,
the sum of T_n(D, z) over even n is at most V(z) (1 - f(s) + ε C_2 e ^ 2 h(s)).
Class HARD: the same inputs as the odd bound. -/
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
  sorry

/-- A member of `primesBelowIn P z` lies in `P`. -/
private theorem mem_primesBelowIn306_set {P : Set ℕ} {z : ℝ} {p : ℕ}
    (hp : p ∈ LeanLab.ChenExplicit.primesBelowIn P z) : p ∈ P := by
  classical
  have h := hp
  simp only [LeanLab.ChenExplicit.primesBelowIn, Finset.mem_filter] at h
  exact h.2

/-- A member of `primesBelowIn P z` lies below `z`. -/
private theorem lt_of_mem_primesBelowIn306 {P : Set ℕ} {z : ℝ} {p : ℕ}
    (hp : p ∈ LeanLab.ChenExplicit.primesBelowIn P z) : (p : ℝ) < z := by
  classical
  have h := hp
  simp only [LeanLab.ChenExplicit.primesBelowIn, Finset.mem_filter, Finset.mem_range] at h
  exact Nat.lt_ceil.mp h.1

/-- The sieve product of BJS displays 29 and 30 is nonnegative. -/
private theorem prod_inv_nonneg306 {P : Set ℕ} {z : ℝ} {g : ArithmeticFunction ℝ}
    (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) {u : ℝ} :
    0 ≤ ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ := by
  classical
  refine Finset.prod_nonneg (fun p hp => ?_)
  obtain ⟨hpS, -⟩ := Finset.mem_filter.mp hp
  obtain ⟨h0, h1⟩ := hgp p (mem_primesBelowIn306_set hpS)
  exact le_of_lt (inv_pos.mpr (by linarith))

/-- LEAF: the constant K of BJS displays 29 and 30 from the strict display 4. With finitely
many primes below z, the ratio of the product to log z / log u has supremum below 1 + ε,
so one K with 1 < K < 1 + ε serves every u. The paper uses this step silently when it
applies Lemma 11 in the proof of Theorem 6, page 16.
Class EASY: the product is a step function of u, constant between consecutive primes. -/
theorem leaf306_uniform_K (P : Set ℕ) (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) (ε : ℝ) (hε : 0 < ε)
    (h4 : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ < (1 + ε) * (log z / log u)) :
    ∃ K : ℝ, 1 < K ∧ K < 1 + ε ∧ ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ ≤ K * (log z / log u) := by
  classical
  have hz1 : (1 : ℝ) < z := by linarith
  have hlogz : 0 < log z := log_pos hz1
  have hlogzn : log z ≠ 0 := ne_of_gt hlogz
  set S := LeanLab.ChenExplicit.primesBelowIn P z with hS
  set V : Finset ℝ := insert 1 ((S.filter (fun p : ℕ => 2 ≤ p)).image
    (fun p : ℕ => (∏ q ∈ S.filter (fun q : ℕ => (p : ℝ) ≤ (q : ℝ)), (1 - g q)⁻¹) *
      (log p / log z))) with hV
  have hmem1 : (1 : ℝ) ∈ V := by rw [hV]; exact Finset.mem_insert_self _ _
  have hVne : V.Nonempty := ⟨1, hmem1⟩
  -- every candidate value of the ratio is below 1 + ε
  have hmax : V.max' hVne < 1 + ε := by
    rw [Finset.max'_lt_iff]
    intro v hv
    rcases Finset.mem_insert.mp (hV ▸ hv) with rfl | hv'
    · linarith
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv'
    obtain ⟨hpS, hp2⟩ := Finset.mem_filter.mp hp
    have hp1 : 1 < p := by omega
    have hlogp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp1)
    have hb := h4 p (by exact_mod_cast hp1) (lt_of_mem_primesBelowIn306 hpS)
    calc (∏ q ∈ S.filter (fun q : ℕ => (p : ℝ) ≤ (q : ℝ)), (1 - g q)⁻¹) * (log p / log z)
        < ((1 + ε) * (log z / log p)) * (log p / log z) :=
          mul_lt_mul_of_pos_right hb (div_pos hlogp hlogz)
      _ = 1 + ε := by field_simp
  refine ⟨(V.max' hVne + (1 + ε)) / 2, ?_, ?_, ?_⟩
  · have h1 : 1 ≤ V.max' hVne := Finset.le_max' V 1 hmem1
    linarith
  · linarith
  intro u hu1 huz
  have hlogu : 0 < log u := log_pos hu1
  have hMle : V.max' hVne ≤ (V.max' hVne + (1 + ε)) / 2 := by linarith
  have hKpos : (0 : ℝ) ≤ (V.max' hVne + (1 + ε)) / 2 := by
    have h1 : 1 ≤ V.max' hVne := Finset.le_max' V 1 hmem1
    linarith
  by_cases hex : ∃ p ∈ S, u ≤ (p : ℝ)
  · obtain ⟨q0, hq0⟩ := hex
    set T := S.filter (fun p : ℕ => u ≤ (p : ℝ)) with hT
    have hTne : T.Nonempty := ⟨q0, by rw [hT]; exact Finset.mem_filter.mpr hq0⟩
    set m := T.min' hTne with hm
    have hmT : m ∈ T := Finset.min'_mem T hTne
    obtain ⟨hmS, hum⟩ := Finset.mem_filter.mp hmT
    have hm1 : (1 : ℝ) < (m : ℝ) := lt_of_lt_of_le hu1 hum
    have hlogm : 0 < log (m : ℝ) := log_pos hm1
    have hT' : T = S.filter (fun q : ℕ => (m : ℝ) ≤ (q : ℝ)) := by
      ext q
      rw [hT, Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨hqS, huq⟩
        exact ⟨hqS, by exact_mod_cast Finset.min'_le T q (Finset.mem_filter.mpr ⟨hqS, huq⟩)⟩
      · rintro ⟨hqS, hmq⟩
        exact ⟨hqS, le_trans hum hmq⟩
    have hm2 : 2 ≤ m := by
      have h2 : 1 < m := by exact_mod_cast hm1
      omega
    have hvmem : (∏ q ∈ S.filter (fun q : ℕ => (m : ℝ) ≤ (q : ℝ)), (1 - g q)⁻¹) *
        (log m / log z) ∈ V := by
      rw [hV]
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨m, Finset.mem_filter.mpr ⟨hmS, hm2⟩, rfl⟩)
    have hvle := Finset.le_max' V _ hvmem
    have hprod : ∏ p ∈ S.filter (fun p : ℕ => u ≤ (p : ℝ)), (1 - g p)⁻¹ =
        ∏ q ∈ S.filter (fun q : ℕ => (m : ℝ) ≤ (q : ℝ)), (1 - g q)⁻¹ := by
      rw [← hT, hT']
    have hPK : ∏ q ∈ S.filter (fun q : ℕ => (m : ℝ) ≤ (q : ℝ)), (1 - g q)⁻¹ ≤
        V.max' hVne * (log z / log m) := by
      calc ∏ q ∈ S.filter (fun q : ℕ => (m : ℝ) ≤ (q : ℝ)), (1 - g q)⁻¹
          = ((∏ q ∈ S.filter (fun q : ℕ => (m : ℝ) ≤ (q : ℝ)), (1 - g q)⁻¹) *
              (log m / log z)) * (log z / log m) := by
            field_simp
        _ ≤ V.max' hVne * (log z / log m) :=
            mul_le_mul_of_nonneg_right hvle (div_nonneg (le_of_lt hlogz) (le_of_lt hlogm))
    have hdivle : log z / log m ≤ log z / log u :=
      div_le_div_of_nonneg_left (le_of_lt hlogz) hlogu (log_le_log (by linarith) hum)
    rw [hprod]
    calc ∏ q ∈ S.filter (fun q : ℕ => (m : ℝ) ≤ (q : ℝ)), (1 - g q)⁻¹
        ≤ V.max' hVne * (log z / log m) := hPK
      _ ≤ (V.max' hVne + (1 + ε)) / 2 * (log z / log u) :=
          mul_le_mul hMle hdivle (div_nonneg (le_of_lt hlogz) (le_of_lt hlogm)) hKpos
  · have hEmpty : S.filter (fun p : ℕ => u ≤ (p : ℝ)) = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr (fun p hp => ?_)
      exact hex ⟨p, (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
    rw [hEmpty, Finset.prod_empty]
    have h1 : 1 ≤ V.max' hVne := Finset.le_max' V 1 hmem1
    have hratio : (1 : ℝ) ≤ log z / log u := by
      rw [le_div_iff₀ hlogu]
      linarith [log_le_log (by linarith : (0:ℝ) < u) (le_of_lt huz)]
    nlinarith [h1, hratio]

open Classical in
/-- Membership in the divisors of `q * N` for a prime `q` not dividing `N`. -/
private theorem mem_divisors_mul_prime306 {N q d : ℕ} (hq : q.Prime) (hNq : ¬ q ∣ N) :
    d ∈ (q * N).divisors ↔ d ∈ N.divisors ∨ ∃ e ∈ N.divisors, q * e = d := by
  classical
  have hN0 : N ≠ 0 := by rintro rfl; exact hNq (dvd_zero q)
  rw [Nat.mem_divisors]
  constructor
  · rintro ⟨hdvd, -⟩
    by_cases hqd : q ∣ d
    · obtain ⟨e, rfl⟩ := hqd
      have he : e ∣ N := (Nat.mul_dvd_mul_iff_left hq.pos).mp hdvd
      exact Or.inr ⟨e, Nat.mem_divisors.mpr ⟨he, hN0⟩, rfl⟩
    · have hcop : d.Coprime q := ((hq.coprime_iff_not_dvd).mpr hqd).symm
      have hdvd' : d ∣ N * q := by rw [Nat.mul_comm]; exact hdvd
      exact Or.inl (Nat.mem_divisors.mpr ⟨hcop.dvd_of_dvd_mul_right hdvd', hN0⟩)
  · rintro (h | ⟨e, he, rfl⟩)
    · refine ⟨?_, Nat.mul_ne_zero hq.ne_zero hN0⟩
      have h2 : d ∣ N * q := ((Nat.mem_divisors.mp h).1).mul_right q
      rwa [Nat.mul_comm N q] at h2
    · refine ⟨?_, Nat.mul_ne_zero hq.ne_zero hN0⟩
      exact (Nat.mul_dvd_mul_iff_left hq.pos).mpr (Nat.mem_divisors.mp he).1

/-- For a prime `q` not dividing `N` the divisors of `q * N` are the divisors of `N` together
with their multiples by `q`. -/
private theorem divisors_mul_prime306 {N q : ℕ} (hq : q.Prime) (hNq : ¬ q ∣ N) :
    (q * N).divisors = N.divisors ∪ N.divisors.image (fun e => q * e) := by
  classical
  ext d
  rw [mem_divisors_mul_prime306 hq hNq, Finset.mem_union, Finset.mem_image]

/-- Summing over the divisors of `q * N` with `q` prime not dividing `N` splits the last prime
factor off. -/
private theorem sum_divisors_mul_prime306 {N q : ℕ} (hq : q.Prime) (hNq : ¬ q ∣ N)
    (f : ℕ → ℝ) :
    ∑ d ∈ (q * N).divisors, f d = ∑ e ∈ N.divisors, (f e + f (q * e)) := by
  classical
  have hinj : Set.InjOn (fun e : ℕ => q * e) ↑N.divisors := by
    intro a _ b _ hab
    exact Nat.mul_left_cancel hq.pos hab
  have hdisj : Disjoint N.divisors (N.divisors.image (fun e => q * e)) := by
    rw [Finset.disjoint_left]
    rintro a ha ha'
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha'
    have h2 : q * e ∣ N := (Nat.mem_divisors.mp ha).1
    exact hNq (dvd_trans (dvd_mul_right q e) h2)
  rw [divisors_mul_prime306 hq hNq, Finset.sum_union hdisj, Finset.sum_image hinj,
    ← Finset.sum_add_distrib]

/-- The product of `1 - psi p` over a finite set of primes as a Möbius sum over the divisors of
their product, BJS display 11 with `psi` multiplicative. -/
private theorem sum_moebius_mul_prod306 (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (ψ : ℕ → ℝ)
    (h1 : ψ 1 = 1) (hmul : ∀ a b : ℕ, a.Coprime b → ψ (a * b) = ψ a * ψ b) :
    ∑ e ∈ (∏ p ∈ T, p).divisors, (ArithmeticFunction.moebius e : ℝ) * ψ e =
      ∏ p ∈ T, (1 - ψ p) := by
  classical
  induction T using Finset.induction with
  | empty => simp [h1, Nat.divisors_one]
  | insert q T hqT ih =>
      have hq : q.Prime := hT q (Finset.mem_insert_self q T)
      have hT' : ∀ p ∈ T, p.Prime := fun p hp => hT p (Finset.mem_insert_of_mem hp)
      have hqN : ¬ q ∣ ∏ p ∈ T, p := by
        intro h
        obtain ⟨r, hr, hqr⟩ := (Prime.dvd_finsetProd_iff hq.prime (fun x => x)).mp h
        have hqr' : q = r := (Nat.prime_dvd_prime_iff_eq hq (hT' r hr)).mp hqr
        exact hqT (hqr'.symm ▸ hr)
      rw [Finset.prod_insert hqT, sum_divisors_mul_prime306 hq hqN]
      have hterm : ∀ e ∈ (∏ p ∈ T, p).divisors,
          (ArithmeticFunction.moebius e : ℝ) * ψ e +
            (ArithmeticFunction.moebius (q * e) : ℝ) * ψ (q * e) =
          (1 - ψ q) * ((ArithmeticFunction.moebius e : ℝ) * ψ e) := by
        intro e he
        have heN : e ∣ ∏ p ∈ T, p := (Nat.mem_divisors.mp he).1
        have hqe : ¬ q ∣ e := fun h => hqN (h.trans heN)
        have hcop : q.Coprime e := (hq.coprime_iff_not_dvd).mpr hqe
        have hmu : (ArithmeticFunction.moebius (q * e) : ℝ) =
            -(ArithmeticFunction.moebius e : ℝ) := by
          have hm : ArithmeticFunction.moebius (q * e) =
              ArithmeticFunction.moebius q * ArithmeticFunction.moebius e :=
            ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
          rw [hm, ArithmeticFunction.moebius_apply_prime hq]
          push_cast
          ring
        rw [hmu, hmul q e hcop]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ih hT', Finset.prod_insert hqT]

/-- The Möbius indicator of coprimality: for a finite set of primes, the sum of `mu e` over the
divisors `e` of their product that divide `n` is the indicator of `n` coprime to the product. -/
private theorem sum_moebius_indicator306 (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (n : ℕ) :
    ∑ e ∈ (∏ p ∈ T, p).divisors,
        (ArithmeticFunction.moebius e : ℝ) * (if e ∣ n then (1 : ℝ) else 0) =
      if Nat.Coprime n (∏ p ∈ T, p) then (1 : ℝ) else 0 := by
  classical
  induction T using Finset.induction with
  | empty =>
      simp [Nat.divisors_one, ArithmeticFunction.moebius_apply_one]
  | insert q T hqT ih =>
      have hq : q.Prime := hT q (Finset.mem_insert_self q T)
      have hT' : ∀ p ∈ T, p.Prime := fun p hp => hT p (Finset.mem_insert_of_mem hp)
      have hqN : ¬ q ∣ ∏ p ∈ T, p := by
        intro h
        obtain ⟨r, hr, hqr⟩ := (Prime.dvd_finsetProd_iff hq.prime (fun x => x)).mp h
        have hqr' : q = r := (Nat.prime_dvd_prime_iff_eq hq (hT' r hr)).mp hqr
        exact hqT (hqr'.symm ▸ hr)
      rw [Finset.prod_insert hqT, sum_divisors_mul_prime306 hq hqN]
      have hterm : ∀ e ∈ (∏ p ∈ T, p).divisors,
          (ArithmeticFunction.moebius e : ℝ) * (if e ∣ n then (1 : ℝ) else 0) +
            (ArithmeticFunction.moebius (q * e) : ℝ) * (if q * e ∣ n then (1 : ℝ) else 0) =
          ((ArithmeticFunction.moebius e : ℝ) * (if e ∣ n then (1 : ℝ) else 0)) *
            (1 - (if q ∣ n then (1 : ℝ) else 0)) := by
        intro e he
        have heN : e ∣ ∏ p ∈ T, p := (Nat.mem_divisors.mp he).1
        have hqe : ¬ q ∣ e := fun h => hqN (h.trans heN)
        have hcop : q.Coprime e := (hq.coprime_iff_not_dvd).mpr hqe
        have hmu : (ArithmeticFunction.moebius (q * e) : ℝ) =
            -(ArithmeticFunction.moebius e : ℝ) := by
          have hm : ArithmeticFunction.moebius (q * e) =
              ArithmeticFunction.moebius q * ArithmeticFunction.moebius e :=
            ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
          rw [hm, ArithmeticFunction.moebius_apply_prime hq]
          push_cast
          ring
        have hiff : (q * e ∣ n) ↔ (q ∣ n ∧ e ∣ n) := by
          constructor
          · intro h
            exact ⟨dvd_trans (dvd_mul_right q e) h, dvd_trans (dvd_mul_left e q) h⟩
          · rintro ⟨h1, h2⟩
            exact hcop.mul_dvd_of_dvd_of_dvd h1 h2
        rw [hmu]
        by_cases h1 : q ∣ n <;> by_cases h2 : e ∣ n <;> simp [hiff, h1, h2]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ih hT']
      have hstep : (if Nat.Coprime n (∏ p ∈ T, p) then (1 : ℝ) else 0) *
          (1 - (if q ∣ n then (1 : ℝ) else 0)) =
          if Nat.Coprime n (q * ∏ p ∈ T, p) then (1 : ℝ) else 0 := by
        by_cases h1 : q ∣ n
        · have hcn : ¬ Nat.Coprime n (q * ∏ p ∈ T, p) := by
            intro h
            have hcq : Nat.Coprime n q := (Nat.coprime_mul_iff_right.mp h).1
            exact ((hq.coprime_iff_not_dvd).mp hcq.symm) h1
          simp [h1, hcn]
        · have hcq : Nat.Coprime n q := ((hq.coprime_iff_not_dvd).mpr h1).symm
          have hiff2 : Nat.Coprime n (q * ∏ p ∈ T, p) ↔ Nat.Coprime n (∏ p ∈ T, p) := by
            rw [Nat.coprime_mul_iff_right]
            exact ⟨fun h => h.2, fun h => ⟨hcq, h⟩⟩
          simp only [hiff2]
          simp [h1]
      exact hstep

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
#print axioms theorem6_of_leaves306

end LeanLab.Cai2002

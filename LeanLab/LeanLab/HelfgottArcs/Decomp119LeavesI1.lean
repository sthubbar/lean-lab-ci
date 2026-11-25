/-
P0013 page 70, the Type I logarithmic bound before equation 5.58, split into leaves.
The original statement is Decomp119.typeI₁_bound; this file imports Decomp119,
so the assembly is stated here as typeI₁_bound_of_leaves.
The paper works with a new approximation 2α = a'/q' + δ'/x with q' ≤ Q = x^{2/3}/(500√6).
The leaves keep that re-approximation explicit, since the totient check of page 70 fails
for denominators as large as the 3/4 x^{2/3} allowed by MinorHyp, for example at
x = 2.16e20 and q the product of the primes up to 37.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Decomp119

namespace LeanLab.HelfgottArcs.Decomp119LeavesI1
open LeanLab.HelfgottArcs.Decomp119

/-- LEAF: page 70, equation 5.2 for the second choice of U, V, Q and the new
approximation of 2α with denominator q' ≤ Q, in case a or case b. Class HARD.
P0013 page 70, display ending in 1.063/10000 x^{2/3} (log x)^2, c'_0 = 0.798437 of
page 59; the term 0.090843 x^{2/3} of the next display is kept and the squared log
coefficient is taken as the larger 0.001063. -/
theorem typeI₁_eq52 (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ)
    (h : MinorHyp x α a q δ) (hq : x ^ ((1 : ℝ) / 3) / 6 < q) :
    ∃ q' : ℕ, ∃ δ' : ℝ, 1 ≤ q' ∧ (q' : ℝ) ≤ x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6) ∧
      (x ^ ((1 : ℝ) / 3) / 6 < q' ∨
        (8 < |δ'| ∧ 8 * (x ^ ((1 : ℝ) / 3) / 6) < |δ'| * q')) ∧
      ‖I₁ α x‖ ≤ x / q' * min 1 (0.798437 / δ' ^ 2) *
          (2 / 3 * Real.log x - 4.99944 + 1.00303 * ((q' : ℝ) / Nat.totient q')) +
        0.090843 * x ^ ((2 : ℝ) / 3) + 0.001063 * x ^ ((2 : ℝ) / 3) * Real.log x ^ 2 := by
  sorry

/-! Helpers for totient_ratio_bound, session S124. The primorial argument of page 70:
q/φ(q) is a product of p/(p-1) over the primes p dividing q, and for every finite set S
of primes 1.00303 ∏ p/(p-1) ≤ 0.04905 log ∏ p + 5.347. Primes up to 43 are checked
exhaustively over all subsets by a kernel computation with rational lower bounds for
log p; a larger prime p is added by induction using the bound primorial ≤ 4^n. -/
namespace TotientRatio
/-- Integer form of the leaf test 1.00303 N/D ≤ 0.04905 L/20 0.6931471803 + 5.347. -/
def leafOK (N D L : ℕ) : Bool :=
  decide (100303 * N * 200000000000 ≤ (4905 * L * 6931471803 + 106940000000000000) * D)

/-- Exhaustive check over all subsets of a list of pairs prime, scaled log lower bound. -/
def chk : List (ℕ × ℕ) → ℕ → ℕ → ℕ → Bool
  | [], N, D, L => leafOK N D L
  | pk :: t, N, D, L => chk t N D L && chk t (N * pk.1) (D * (pk.1 - 1)) (L + pk.2)

theorem leafOK_sound {N D L : ℕ} (hD : 0 < D) (h : leafOK N D L = true) :
    1.00303 * ((N : ℝ) / D) ≤ 0.04905 * ((L : ℝ) / 20 * 0.6931471803) + 5.347 := by
  simp only [leafOK, decide_eq_true_eq] at h
  have h' : (100303 * N * 200000000000 : ℝ) ≤
      (4905 * L * 6931471803 + 106940000000000000) * D := by exact_mod_cast h
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [mul_div_assoc', div_le_iff₀ hD']
  nlinarith

theorem log_lb (p k : ℕ) (_hp : 0 < p) (h : 2 ^ k ≤ p ^ 20) :
    (k : ℝ) / 20 * 0.6931471803 ≤ Real.log p := by
  have h1 : (k : ℝ) * Real.log 2 ≤ 20 * Real.log p := by
    have h2 : ((2 : ℝ)) ^ k ≤ (p : ℝ) ^ 20 := by exact_mod_cast h
    have h3 := Real.log_le_log (by positivity) h2
    rwa [Real.log_pow, Real.log_pow] at h3
  have := Real.log_two_gt_d9
  have hk : (0 : ℝ) ≤ k := by positivity
  nlinarith

theorem chk_sound : ∀ (l : List (ℕ × ℕ)) (N D L : ℕ),
    (∀ pk ∈ l, 2 ≤ pk.1 ∧ (pk.2 : ℝ) / 20 * 0.6931471803 ≤ Real.log pk.1) → 0 < D →
    chk l N D L = true → ∀ S ⊆ (l.map Prod.fst).toFinset,
    1.00303 * ((N : ℝ) / D) * ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1)) ≤
      0.04905 * ((L : ℝ) / 20 * 0.6931471803 + ∑ p ∈ S, Real.log p) + 5.347
  | [], N, D, L, _, hD, h, S, hS => by
      have hS0 : S = ∅ := by simpa using hS
      subst hS0
      simpa using leafOK_sound hD h
  | pk :: t, N, D, L, hl, hD, h, S, hS => by
      simp only [chk, Bool.and_eq_true] at h
      obtain ⟨hp2, hlog⟩ := hl pk (by simp)
      have hl' : ∀ q ∈ t, 2 ≤ q.1 ∧ (q.2 : ℝ) / 20 * 0.6931471803 ≤ Real.log q.1 :=
        fun q hq => hl q (by simp [hq])
      by_cases hpS : pk.1 ∈ S
      · have hS' : S.erase pk.1 ⊆ (t.map Prod.fst).toFinset := by
          intro y hy
          have hyS := Finset.mem_of_mem_erase hy
          have hne := Finset.ne_of_mem_erase hy
          have := hS hyS
          simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert] at this
          rcases this with h1 | h1
          · exact absurd h1 hne
          · exact h1
        have hD2 : 0 < D * (pk.1 - 1) := Nat.mul_pos hD (by omega)
        have ih := chk_sound t _ _ _ hl' hD2 h.2 (S.erase pk.1) hS'
        rw [← Finset.mul_prod_erase S _ hpS, ← Finset.add_sum_erase S _ hpS]
        have hc : ((pk.1 - 1 : ℕ) : ℝ) = (pk.1 : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        push_cast at ih
        rw [hc] at ih
        have ha : (1 : ℝ) < pk.1 := by exact_mod_cast (show 1 < pk.1 by omega)
        have ha1 : (pk.1 : ℝ) - 1 ≠ 0 := by linarith
        have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
        have heq : 1.00303 * ((N : ℝ) / D) * ((pk.1 : ℝ) / ((pk.1 : ℝ) - 1) *
            ∏ p ∈ S.erase pk.1, ((p : ℝ) / ((p : ℝ) - 1))) =
            1.00303 * ((N : ℝ) * pk.1 / (D * ((pk.1 : ℝ) - 1))) *
            ∏ p ∈ S.erase pk.1, ((p : ℝ) / ((p : ℝ) - 1)) := by
          field_simp
        rw [heq]
        refine ih.trans ?_
        have : ((L : ℝ) + pk.2) / 20 * 0.6931471803 =
            (L : ℝ) / 20 * 0.6931471803 + (pk.2 : ℝ) / 20 * 0.6931471803 := by ring
        rw [this]
        linarith
      · have hS' : S ⊆ (t.map Prod.fst).toFinset := by
          intro y hy
          have := hS hy
          simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert] at this
          rcases this with h1 | h1
          · exact absurd (h1 ▸ hy) hpS
          · exact h1
        exact chk_sound t N D L hl' hD h.1 S hS'

/-- The fourteen primes up to 43 with k = floor of 20 log_2 p. -/
def baseList : List (ℕ × ℕ) :=
  [(2, 20), (3, 31), (5, 46), (7, 56), (11, 69), (13, 74), (17, 81), (19, 84), (23, 90),
    (29, 97), (31, 99), (37, 104), (41, 107), (43, 108)]

theorem base_chk : chk baseList 1 1 0 = true := by decide +kernel

theorem base_hyp : ∀ pk ∈ baseList,
    2 ≤ pk.1 ∧ (pk.2 : ℝ) / 20 * 0.6931471803 ≤ Real.log pk.1 := by
  intro pk hpk
  simp only [baseList, List.mem_cons, List.not_mem_nil, or_false] at hpk
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := hpk
  all_goals exact ⟨by norm_num, log_lb _ _ (by norm_num) (by norm_num)⟩

theorem base_mem : ∀ y < 47, y.Prime → y ∈ (baseList.map Prod.fst).toFinset := by
  decide +kernel

theorem log_four_lt : Real.log 4 < 1.3863 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [h]; linarith [Real.log_two_lt_d9]

/-- Each prime p has p/(p-1) at least 1. -/
theorem ratio_one_le {p : ℕ} (hp : p.Prime) : 1 ≤ (p : ℝ) / ((p : ℝ) - 1) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [le_div_iff₀ (by linarith)]; linarith

/-- The elementary primorial bound for every finite set of primes. -/
theorem key : ∀ N : ℕ, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p ≤ N) →
    1.00303 * ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1)) ≤
      0.04905 * Real.log (∏ p ∈ S, (p : ℝ)) + 5.347 := by
  have base : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p ≤ 46) →
      1.00303 * ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1)) ≤
        0.04905 * Real.log (∏ p ∈ S, (p : ℝ)) + 5.347 := by
    intro S hS
    have hsub : S ⊆ (baseList.map Prod.fst).toFinset := fun y hy =>
      base_mem y (by have := (hS y hy).2; omega) (hS y hy).1
    have h := chk_sound baseList 1 1 0 base_hyp one_pos base_chk S hsub
    rw [Real.log_prod (fun p hp => by
      have := (hS p hp).1.pos; positivity)]
    simpa using h
  intro N
  induction N with
  | zero => intro S hS; exact base S (fun p hp => ⟨(hS p hp).1, by have := (hS p hp).2; omega⟩)
  | succ N ih =>
    intro S hS
    by_cases hN : N + 1 ≤ 46
    · exact base S (fun p hp => ⟨(hS p hp).1, le_trans (hS p hp).2 hN⟩)
    by_cases hpS : N + 1 ∈ S
    swap
    · refine ih S (fun p hp => ⟨(hS p hp).1, ?_⟩)
      have h1 := (hS p hp).2
      have h2 : p ≠ N + 1 := fun h => hpS (h ▸ hp)
      omega
    have hS' : ∀ p ∈ S.erase (N + 1), p.Prime ∧ p ≤ N := by
      intro p hp
      have h1 := hS p (Finset.mem_of_mem_erase hp)
      have h2 := Finset.ne_of_mem_erase hp
      exact ⟨h1.1, by omega⟩
    set T : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime with hTdef
    have hT : ∀ p ∈ T, p.Prime ∧ p ≤ N := by
      intro p hp
      rw [hTdef, Finset.mem_filter, Finset.mem_range] at hp
      exact ⟨hp.2, by omega⟩
    have hsub : S.erase (N + 1) ⊆ T := by
      intro p hp
      have := hS' p hp
      rw [hTdef, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, this.1⟩
    have ihS := ih _ hS'
    have ihT := ih T hT
    set F' := ∏ p ∈ S.erase (N + 1), ((p : ℝ) / ((p : ℝ) - 1)) with hF'
    have hFT : F' ≤ ∏ p ∈ T, ((p : ℝ) / ((p : ℝ) - 1)) := by
      apply Finset.prod_le_prod_of_subset_of_one_le₀ hsub
      · intro p hp
        exact le_trans zero_le_one (ratio_one_le (hS' p hp).1)
      · intro p hp _
        exact ratio_one_le (hT p hp).1
    have hTprod : ∏ p ∈ T, (p : ℝ) = ((primorial N : ℕ) : ℝ) := by
      rw [primorial, Nat.cast_prod]
    have hN0 : N ≠ 0 := by omega
    have hlogT : Real.log (∏ p ∈ T, (p : ℝ)) ≤ N * Real.log 4 := by
      rw [hTprod]
      have h1 : ((primorial N : ℕ) : ℝ) ≤ (4 : ℝ) ^ N := by
        exact_mod_cast (primorial_lt_four_pow N hN0).le
      have h0 : (0 : ℝ) < ((primorial N : ℕ) : ℝ) := by exact_mod_cast primorial_pos N
      have := Real.log_le_log h0 h1
      rwa [Real.log_pow] at this
    have hNr : (46 : ℝ) ≤ N := by exact_mod_cast (show 46 ≤ N by omega)
    have hcF : 1.00303 * F' ≤ 0.04905 * (N * Real.log 4) + 5.347 := by
      have : 1.00303 * F' ≤ 1.00303 * ∏ p ∈ T, ((p : ℝ) / ((p : ℝ) - 1)) := by linarith
      linarith
    have hlog4 := log_four_lt
    have hlog47 : (111 : ℕ) / 20 * 0.6931471803 ≤ Real.log (47 : ℕ) :=
      log_lb 47 111 (by norm_num) (by norm_num)
    have hlogp : Real.log 47 ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
      apply Real.log_le_log (by norm_num)
      push_cast; linarith
    push_cast at hlog47 hlogp
    have hNpos : (0 : ℝ) < N := by linarith
    have hdiv : 1.00303 * F' / N ≤ 0.04905 * Real.log 4 + 5.347 / 46 := by
      rw [div_le_iff₀ hNpos]
      have : 5.347 / 46 * (N : ℝ) ≥ 5.347 := by
        rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]; nlinarith
      nlinarith
    rw [← Finset.mul_prod_erase S _ hpS, ← Finset.mul_prod_erase S (fun p => (p : ℝ)) hpS]
    have hP0 : (0 : ℝ) < ∏ p ∈ S.erase (N + 1), (p : ℝ) :=
      Finset.prod_pos (fun p hp => by have := (hS' p hp).1.pos; positivity)
    rw [Real.log_mul (by positivity) hP0.ne']
    rw [← hF']
    have hsplit : 1.00303 * (((N + 1 : ℕ) : ℝ) / (((N + 1 : ℕ) : ℝ) - 1) * F') =
        1.00303 * F' + 1.00303 * F' / N := by
      have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
      push_cast
      rw [show (N : ℝ) + 1 - 1 = N by ring]
      field_simp
    rw [hsplit]
    have e : Real.log ((N + 1 : ℕ) : ℝ) = Real.log ((N : ℝ) + 1) := by push_cast; rfl
    rw [e]
    nlinarith

/-- q/φ(q) as the product of p/(p-1) over the prime factors of q. -/
theorem ratio_eq_prod (q : ℕ) (hq : 1 ≤ q) :
    (q : ℝ) / Nat.totient q = ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
  have h := Nat.totient_mul_prod_primeFactors q
  have hR : (Nat.totient q : ℝ) * ∏ p ∈ q.primeFactors, (p : ℝ) =
      (q : ℝ) * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    have h' := congrArg (fun n : ℕ => (n : ℝ)) h
    simp only [Nat.cast_mul, Nat.cast_prod] at h'
    rw [h']
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]; simp
  have ht0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hD0 : (0 : ℝ) < ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  rw [Finset.prod_div_distrib, div_eq_div_iff ht0.ne' hD0.ne']
  linarith

end TotientRatio

/-- LEAF: page 70, q'/φ(q') ≤ ̥(Q) with ̥ as in display 5.55, and the check
1.00303 ̥(Q) ≤ 0.0327 log x + 4.99944. Class HARD. P0013 page 70, lines after the
display for S_{I,1}; an explicit Rosser and Schoenfeld type bound for q/φ(q). -/
theorem totient_ratio_bound (x : ℝ) (hx : 2.16e20 ≤ x) (q' : ℕ) (hq1 : 1 ≤ q')
    (hqQ : (q' : ℝ) ≤ x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6)) :
    1.00303 * ((q' : ℝ) / Nat.totient q') ≤ 0.0327 * Real.log x + 4.99944 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hk := TotientRatio.key q' q'.primeFactors (fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors hp, Nat.le_of_mem_primeFactors hp⟩)
  rw [TotientRatio.ratio_eq_prod q' hq1]
  have hP0 : (0 : ℝ) < ∏ p ∈ q'.primeFactors, (p : ℝ) :=
    Finset.prod_pos (fun p hp => by
      have := (Nat.prime_of_mem_primeFactors hp).pos; positivity)
  have hPq : ∏ p ∈ q'.primeFactors, (p : ℝ) ≤ q' := by
    have := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q')
    rw [← Nat.cast_prod]; exact_mod_cast this
  have hs6 : (2.448 : ℝ) ≤ Real.sqrt 6 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hc0 : (0 : ℝ) < 500 * Real.sqrt 6 := by positivity
  have hlog1224 : (205 : ℕ) / 20 * 0.6931471803 ≤ Real.log (1224 : ℕ) :=
    TotientRatio.log_lb 1224 205 (by norm_num) (by norm_num)
  push_cast at hlog1224
  have hlc : Real.log 1224 ≤ Real.log (500 * Real.sqrt 6) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hq0 : (0 : ℝ) < q' := by exact_mod_cast hq1
  have hlq : Real.log (q' : ℝ) ≤ 2 / 3 * Real.log x - Real.log (500 * Real.sqrt 6) := by
    have h1 := Real.log_le_log hq0 hqQ
    rw [Real.log_div (by positivity) hc0.ne', Real.log_rpow hx0] at h1
    exact h1
  have hlP := Real.log_le_log hP0 hPq
  nlinarith

/-- Page 70: with q > y = x^{1/3}/6 the factor x/q is at most x/y = 6 x^{2/3}. -/
theorem x_div_q_le (x : ℝ) (q : ℕ) (hx : 0 < x) (hq : x ^ ((1 : ℝ) / 3) / 6 < q) :
    x / q ≤ 6 * x ^ ((2 : ℝ) / 3) := by
  have hy : 0 < x ^ ((1 : ℝ) / 3) / 6 := by positivity
  have hq0 : (0 : ℝ) < q := hy.trans hq
  have hsplit : x = x ^ ((1 : ℝ) / 3) * x ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_add hx]; norm_num
  rw [div_le_iff₀ hq0]
  calc x = 6 * x ^ ((2 : ℝ) / 3) * (x ^ ((1 : ℝ) / 3) / 6) := by
        nth_rewrite 1 [hsplit]; ring
    _ ≤ 6 * x ^ ((2 : ℝ) / 3) * q := by
        apply mul_le_mul_of_nonneg_left hq.le; positivity

/-- Page 70: in case a or case b the factor x/q' min(1, c'_0/δ'^2) is at most x/y. -/
theorem case_factor_le (x : ℝ) (hx : 0 < x) (q' : ℕ) (δ' : ℝ) (hq1 : 1 ≤ q')
    (hc : x ^ ((1 : ℝ) / 3) / 6 < q' ∨
      (8 < |δ'| ∧ 8 * (x ^ ((1 : ℝ) / 3) / 6) < |δ'| * q')) :
    x / q' * min 1 (0.798437 / δ' ^ 2) ≤ 6 * x ^ ((2 : ℝ) / 3) := by
  have hq0 : (0 : ℝ) < q' := by exact_mod_cast hq1
  have hM0 : 0 ≤ x / q' := by positivity
  rcases hc with hc | ⟨hd, hdq⟩
  · calc x / q' * min 1 (0.798437 / δ' ^ 2) ≤ x / q' * 1 :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hM0
      _ ≤ _ := by rw [mul_one]; exact x_div_q_le x q' hx hc
  · set y := x ^ ((1 : ℝ) / 3) / 6 with hy
    have hy0 : 0 < y := by positivity
    have hsplit : x = 6 * x ^ ((2 : ℝ) / 3) * y := by
      have hs : x = x ^ ((1 : ℝ) / 3) * x ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_add hx]; norm_num
      rw [hy]; nth_rewrite 1 [hs]; ring
    have hd0 : 0 < |δ'| := by linarith
    have hsq : δ' ^ 2 = |δ'| * |δ'| := by rw [← sq_abs]; ring
    have hbig : 64 * y < q' * δ' ^ 2 := by
      rw [hsq]; nlinarith
    have hpos : 0 < (q' : ℝ) * δ' ^ 2 := by linarith
    calc x / q' * min 1 (0.798437 / δ' ^ 2) ≤ x / q' * (0.798437 / δ' ^ 2) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hM0
      _ = x * 0.798437 / (q' * δ' ^ 2) := by
          field_simp
      _ ≤ x / y := by
          rw [div_le_div_iff₀ hpos hy0]; nlinarith
      _ = 6 * x ^ ((2 : ℝ) / 3) := by
          rw [div_eq_iff hy0.ne']; exact hsplit

/-- Assembly of Decomp119.typeI₁_bound from the two leaves, exact parent statement. -/
theorem typeI₁_bound_of_leaves (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ)
    (h : MinorHyp x α a q δ) (hq : x ^ ((1 : ℝ) / 3) / 6 < q) :
    ‖I₁ α x‖ ≤ 4.1982 * x ^ ((2 : ℝ) / 3) * Real.log x +
      0.001063 * x ^ ((2 : ℝ) / 3) * Real.log x ^ 2 := by
  obtain ⟨q', δ', hq1, hqQ, hc, h1⟩ := typeI₁_eq52 x α a q δ h hq
  have hx : 2.16e20 ≤ x := h.1
  have h2 := totient_ratio_bound x hx q' hq1 hqQ
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hL : 46.45 < Real.log x :=
    MinorMain.L_bounds.1.trans_le (Real.log_le_log (by norm_num) hx)
  have hq0 : (0 : ℝ) < q' := by exact_mod_cast hq1
  have hmin0 : 0 ≤ min (1 : ℝ) (0.798437 / δ' ^ 2) := le_min (by norm_num) (by positivity)
  have hrat : 1 ≤ (q' : ℝ) / Nat.totient q' := by
    have ht : (Nat.totient q' : ℝ) ≤ q' := by exact_mod_cast Nat.totient_le q'
    have ht0 : (0 : ℝ) < Nat.totient q' := by
      have : 0 < Nat.totient q' := Nat.totient_pos.mpr hq1
      exact_mod_cast this
    rw [le_div_iff₀ ht0]; linarith
  set F := 2 / 3 * Real.log x - 4.99944 + 1.00303 * ((q' : ℝ) / Nat.totient q') with hF
  have hF0 : 0 ≤ F := by rw [hF]; nlinarith
  have hFle : F ≤ 0.69937 * Real.log x := by rw [hF]; linarith
  have hMm := case_factor_le x hx0 q' δ' hq1 hc
  set P := x ^ ((2 : ℝ) / 3) with hP
  have hP0 : 0 ≤ P := by positivity
  have hprod : x / q' * min (1 : ℝ) (0.798437 / δ' ^ 2) * F ≤ 6 * P * (0.69937 * Real.log x) :=
    mul_le_mul hMm hFle hF0 (by positivity)
  have hlow : 0.090843 * P ≤ 0.002 * P * Real.log x := by nlinarith
  nlinarith

end LeanLab.HelfgottArcs.Decomp119LeavesI1

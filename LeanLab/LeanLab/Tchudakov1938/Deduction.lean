/-
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1614Z-cloud28, unit U-5701, paper P0064.

# Chudakov 1938, Izv. Akad. Nauk SSSR Ser. Mat. 2:1, 25-40: the statements and the deductions

Read from `papers/P0064.pdf`, page images of pp. 25-30.

* p. 25-26: `ν(x)` is the number of even numbers between 6 and `x` that are not a sum of two odd
  primes. Inequality (1), p. 26: `ν(x) < C_M x / (lg x)^M` for every `M > 0`, with `C_M > 0`
  depending only on `M`. Here `nu` and `theorem1_stmt`.
* p. 26: (1) gives Vinogradov's theorem: by Chebyshev the odd primes `≤ x - 6` number more than
  `β x / lg x`; for odd `x` large the numbers `x - p_i` are even, `≥ 6`, and more than `ν(x)`,
  so one is a sum of two odd primes. Here `vinogradov_of_theorem1`, with the lab's explicit
  Chebyshev bound `π(n) ≥ (0.9212 n - 5 log n)/log n` in place of `β`.
* p. 28, Lemma 2: `Σ_{m'+m''=m, m',m'' ≥ 3} 1/(lg m' lg m'') ≥ (m - 5)/lg² m`, the first step of its
  proof; `lemma2_first`.

`theorem1_of_logPowerSaving` derives (1) from the lab's `ExceptionalSet.LogPowerSaving`, since
an even `n ≥ 6` that is a sum of two primes is a sum of two odd primes. Binary Goldbach is OPEN;
(1) says the exceptions, if any, are rare.
-/
import Mathlib
import LeanLab.ExceptionalSet.Statements
import LeanLab.ChebyshevExplicit.Psi30

namespace LeanLab.Tchudakov1938
open Real Finset

attribute [local instance] Classical.propDecidable

/-- `n` is a sum of two odd primes. -/
def IsOddGoldbachSum (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ p + q = n

/-- `n` is a sum of three odd primes. -/
def IsOddTernarySum (n : ℕ) : Prop :=
  ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ Odd p ∧ Odd q ∧ Odd r ∧ p + q + r = n

/-- Chudakov's `ν(x)`, p. 25: the even `n` with `6 ≤ n ≤ x` that are not a sum of two odd primes. -/
noncomputable def nu (x : ℕ) : ℕ :=
  ((Finset.Icc 6 x).filter (fun n => Even n ∧ ¬ IsOddGoldbachSum n)).card

/-- Inequality (1), p. 26: for every `M > 0` there is `C_M > 0` with `ν(x) < C_M x/(lg x)^M`.
The paper takes `x` large, `x > c₀`; the form here holds for every `x ≥ 2`, which is the same
statement after enlarging `C_M`. `lg` is the natural logarithm, p. 26 writes `lg e^{c₂/β} = c₂/β`;
another base changes only `C_M`. -/
def theorem1_stmt : Prop :=
  ∀ M : ℝ, 0 < M → ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 2 ≤ x → (nu x : ℝ) < C * x / Real.log x ^ M

/-- An even `n ≥ 6` that is a sum of two primes is a sum of two odd primes. -/
theorem oddGoldbach_of_goldbach {n : ℕ} (he : Even n) (h6 : 6 ≤ n) (h : IsGoldbachSum n) :
    IsOddGoldbachSum n := by
  obtain ⟨p, q, hp, hq, hpq⟩ := h
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hqe : Even q := by
      have : q = n - 2 := by omega
      subst this; exact (Nat.even_sub (by omega)).mpr (by simp [he])
    have := (hq.even_iff).mp hqe; omega
  have hq2 : q ≠ 2 := by
    rintro rfl
    have hpe : Even p := by
      have : p = n - 2 := by omega
      subst this; exact (Nat.even_sub (by omega)).mpr (by simp [he])
    have := (hp.even_iff).mp hpe; omega
  exact ⟨p, q, hp, hq, hp.odd_of_ne_two hp2, hq.odd_of_ne_two hq2, hpq⟩

/-- `ν(x) ≤ E(x)`, the lab's exceptional set count. -/
theorem nu_le_E (x : ℕ) : nu x ≤ ExceptionalSet.E x := by
  unfold nu ExceptionalSet.E
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  refine ⟨⟨by omega, hn.1.2⟩, hn.2.1, fun h => hn.2.2 ?_⟩
  exact oddGoldbach_of_goldbach hn.2.1 hn.1.1 h

/-- (1) follows from the lab's `LogPowerSaving`. -/
theorem theorem1_of_logPowerSaving (h : ExceptionalSet.LogPowerSaving) : theorem1_stmt := by
  intro M hM
  obtain ⟨C, hC⟩ := h M hM
  refine ⟨max C 0 + 1, by positivity, fun x hx => ?_⟩
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hpos : 0 < (x : ℝ) / Real.log x ^ M := div_pos (by linarith) (Real.rpow_pos_of_pos hlog M)
  have h1 : (nu x : ℝ) ≤ C * x / Real.log x ^ M :=
    (Nat.cast_le.mpr (nu_le_E x)).trans (hC x hx)
  rw [mul_div_assoc] at h1 ⊢
  nlinarith [le_max_left C 0]

/-- The odd primes `p ≤ y`, that is the primes in `[3, y]`. -/
theorem card_oddPrimes (y : ℕ) :
    ((Finset.Icc 3 y).filter Nat.Prime).card + 1 ≥ Nat.primeCounting y := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  calc ((Finset.range (y + 1)).filter Nat.Prime).card
      ≤ ((insert 2 ((Finset.Icc 3 y).filter Nat.Prime))).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_range] at hp
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
        by_cases h2 : p = 2
        · exact Or.inl h2
        · exact Or.inr ⟨⟨by have := hp.2.two_le; omega, by omega⟩, hp.2⟩
    _ ≤ _ := Finset.card_insert_le _ _

/-- The counting step on p. 26: if odd `x` is not a sum of three odd primes, then every odd prime
`p ≤ x - 6` gives an even `x - p ∈ [6, x]` that is not a sum of two odd primes, so
`π(x - 6) ≤ ν(x) + 1`. -/
theorem primeCounting_le_nu {x : ℕ} (hx : Odd x) (h : ¬ IsOddTernarySum x) :
    Nat.primeCounting (x - 6) ≤ nu x + 1 := by
  refine le_trans (card_oddPrimes (x - 6)) ?_
  · apply Nat.add_le_add_right
    unfold nu
    refine Finset.card_le_card_of_injOn (fun p => x - p) ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hp
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq]
      have hpo : Odd p := hp.2.odd_of_ne_two (by omega)
      refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
      · exact (Nat.Odd.sub_odd hx hpo)
      · rintro ⟨a, b, ha, hb, hao, hbo, hab⟩
        exact h ⟨a, b, p, ha, hb, hp.2, hao, hbo, hpo, by omega⟩
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hp hq
      simp only at hpq
      omega

/-- Chudakov's deduction of Vinogradov's theorem from (1), p. 26, with the lab's explicit
Chebyshev bound: every sufficiently large odd `x` is a sum of three odd primes. -/
theorem vinogradov_of_theorem1 (h : theorem1_stmt) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → Odd x → IsOddTernarySum x := by
  obtain ⟨C, hC, hν⟩ := h 2 two_pos
  -- choose y large: log y ≥ 10 C + 10 and y ≥ 100 (log y + 1)
  have hev : ∀ᶠ y : ℕ in Filter.atTop,
      10 * C + 10 ≤ Real.log y ∧ 100 * (Real.log y + 1) ≤ y := by
    have h1 : ∀ᶠ y : ℕ in Filter.atTop, 10 * C + 10 ≤ Real.log y :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
    have h2 : ∀ᶠ y : ℝ in Filter.atTop, 100 * (Real.log y + 1) ≤ y := by
      have := (Real.isLittleO_log_id_atTop).bound (c := 1 / 200) (by norm_num)
      filter_upwards [this, Filter.eventually_ge_atTop (200 : ℝ)] with y hy hy2
      rw [Real.norm_eq_abs, Real.norm_eq_abs, id] at hy
      have h3 : |y| = y := abs_of_pos (by linarith)
      have h4 := le_abs_self (Real.log y)
      rw [h3] at hy
      linarith
    exact h1.and (tendsto_natCast_atTop_atTop.eventually h2)
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max Y 30 + 6, fun x hx hxo => ?_⟩
  by_contra hno
  set y := x - 6 with hy
  have hyY : Y ≤ y := by omega
  have hy30 : 30 ≤ y := by omega
  obtain ⟨hl1, hl2⟩ := hY y hyY
  have hπ := LeanLab.ChebyshevExplicit.pi_ge_chebyshev30 y hy30
  have hcount := primeCounting_le_nu hxo hno
  have hx2 : 2 ≤ x := by omega
  have hνx := hν x hx2
  -- real bookkeeping
  have hyR : (y : ℝ) + 6 = x := by rw [hy]; push_cast [show 6 ≤ x by omega]; ring
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (by omega : 1 < y)
  have hly : 0 < Real.log y := Real.log_pos hy1
  have hlxy : Real.log y ≤ Real.log x := Real.log_le_log (by linarith) (by rw [← hyR]; linarith)
  have hlx : 0 < Real.log x := lt_of_lt_of_le hly hlxy
  have hrp : Real.log x ^ (2 : ℝ) = Real.log x ^ 2 := by norm_cast
  rw [hrp] at hνx
  have hcountR : (Nat.primeCounting y : ℝ) ≤ nu x + 1 := by exact_mod_cast hcount
  -- π(y) log y ≥ 0.9212 y - 5 log y
  have hπ' : 0.9212 * y - 5 * Real.log y ≤ Nat.primeCounting y * Real.log y := by
    rwa [div_le_iff₀ hly] at hπ
  -- ν(x) log y < C x log y / log² x ≤ C x / log y ≤ 2 C y / log y
  have hνy : (nu x : ℝ) * Real.log y ≤ 2 * C * y / Real.log y := by
    have h1 : (nu x : ℝ) * Real.log y ≤ C * x / Real.log x ^ 2 * Real.log y :=
      mul_le_mul_of_nonneg_right hνx.le hly.le
    have h2 : C * x / Real.log x ^ 2 * Real.log y ≤ C * x / Real.log y := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hly]
      have : Real.log y * Real.log y ≤ Real.log x ^ 2 := by nlinarith
      have hCx : 0 ≤ C * x := by positivity
      nlinarith
    have h3 : C * x / Real.log y ≤ 2 * C * y / Real.log y := by
      apply div_le_div_of_nonneg_right _ hly.le
      nlinarith
    linarith
  -- 2 C y / log y ≤ 0.2 y since log y ≥ 10 C
  have hsmall : 2 * C * y / Real.log y ≤ 0.2 * y := by
    rw [div_le_iff₀ hly]; nlinarith
  -- combine: 0.9212 y - 6 log y ≤ (ν + 1) log y - log y + ... contradiction
  have : 0.9212 * (y : ℝ) - 5 * Real.log y ≤ 0.2 * y + Real.log y := by
    nlinarith
  nlinarith

/-- Lemma 2, first step, p. 28: the sum over `m' + m'' = m`, `m', m'' ≥ 3`, of `1/(lg m' lg m'')`
is at least `(m - 5)/lg² m`, for `m ≥ 6`. -/
theorem lemma2_first (m : ℕ) (hm : 6 ≤ m) :
    ((m : ℝ) - 5) / Real.log m ^ 2 ≤
      ∑ a ∈ Finset.Icc 3 (m - 3), 1 / (Real.log a * Real.log (m - a : ℕ)) := by
  have hlm : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hterm : ∀ a ∈ Finset.Icc 3 (m - 3),
      1 / Real.log m ^ 2 ≤ 1 / (Real.log a * Real.log (m - a : ℕ)) := by
    intro a ha
    simp only [Finset.mem_Icc] at ha
    have ha1 : 0 < Real.log a := Real.log_pos (by exact_mod_cast (by omega : 1 < a))
    have hb1 : 0 < Real.log (m - a : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m - a))
    have hal : Real.log a ≤ Real.log m :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < a)) (by exact_mod_cast (by omega : a ≤ m))
    have hbl : Real.log (m - a : ℕ) ≤ Real.log m :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < m - a))
        (by exact_mod_cast (by omega : m - a ≤ m))
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq]; exact mul_le_mul hal hbl hb1.le hlm.le
  calc ((m : ℝ) - 5) / Real.log m ^ 2
      = ∑ _a ∈ Finset.Icc 3 (m - 3), 1 / Real.log m ^ 2 := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        rw [show m - 3 + 1 - 3 = m - 5 by omega]
        push_cast [show 5 ≤ m by omega]; ring
    _ ≤ _ := Finset.sum_le_sum hterm

end LeanLab.Tchudakov1938

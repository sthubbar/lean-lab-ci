import Mathlib
import LeanLab.Common.Goldbach

/-!
# Two OPEN problems, sealed statements and small routes

Unit U-1612, run 20261103T0803Z-22341, 2026-11-03. AI wrote the Lean code. Targets for the network,
no claim of progress. Nothing here counts as progress on Goldbach. Neither is tagged ORIGINAL: both
have a prior statement, see the search record in the out folder, LITSEARCH-U1612-20261103.md.

1. `Euler8n3Statement`: every `8n + 3`, `n ≥ 1`, is an odd square plus twice a prime. Source sentence,
   primepuzzles.net Conjecture 68, reread 2026-11-05: any integer of the form 8n + 3 can be decomposed
   in the sum of a square and double of a prime, attributed to Euler in Pólya, Mathematics and
   Plausible Reasoning II. Pólya was never read here, so the Euler claim rests on this one secondary
   page. The page's own conjecture is Rodríguez's bound `x / (log N)^2 < 2`, the Euler decomposition
   is its premise, and the page carries no Unresolved label. MathOverflow 135608, page blocked for
   fetch, not worked around. POOL line 216. `n = 0` is false, `not_isEuler_three`, so `1 ≤ n` in the
   sealed form is a lab repair, not a transcription. The source and pool wording omit it.
2. `PowerfulPrimeStatement`: every powerful `N > 1` is a prime plus a powerful number. POOL line 194,
   MathOverflow 269080, page blocked for fetch, so the wording is the pool line's and cannot be
   checked against the page, status UNVERIFIED; three web searches found no resolution. `1` must
   count as powerful, `not_rep_four_of_one_excluded`.
-/

namespace LeanLab.OpenProblems.State1612

open LeanLab

/-! ### 1. Euler's 8n + 3 -/

/-- `m` is an odd square plus twice a prime. -/
def IsEuler (m : ℕ) : Prop := ∃ x p : ℕ, Odd x ∧ p.Prime ∧ m = x ^ 2 + 2 * p

/-- **OPEN, sealed.** Every `8n + 3` with `n ≥ 1` is `x² + 2p` with `x` odd, `p` prime. -/
def Euler8n3Statement : Prop := ∀ n : ℕ, 1 ≤ n → IsEuler (8 * n + 3)

/-- `n = 0` is a genuine exception, so `1 ≤ n` is needed. -/
theorem not_isEuler_three : ¬ IsEuler 3 := by
  rintro ⟨x, p, _, hp, e⟩
  have := hp.two_le
  have hx : x ^ 2 ≥ 0 := Nat.zero_le _
  omega

/-- Vacuity: `11 = 1 + 2·5`. -/
theorem isEuler_eleven : IsEuler 11 := ⟨1, 5, by decide, by norm_num, by norm_num⟩

/-- `x` odd gives `x² ≡ 1 mod 8`, so the prime is `1 mod 4`. -/
theorem prime_mod_four {n x p : ℕ} (hx : Odd x) (e : 8 * n + 3 = x ^ 2 + 2 * p) : p % 4 = 1 := by
  obtain ⟨k, rfl⟩ := hx
  have h : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
  have h2 : Even (k * (k + 1)) := Nat.even_mul_succ_self k
  obtain ⟨j, hj⟩ := h2
  rw [h, hj] at e
  omega

/-- The triangular form: `4n + 1 - 2 k (k + 1)` is prime for some `k`, the form of Conjecture 68. -/
theorem isEuler_iff_triangular (n : ℕ) :
    IsEuler (8 * n + 3) ↔ ∃ k p : ℕ, p.Prime ∧ 4 * n + 1 = p + 2 * k * (k + 1) := by
  constructor
  · rintro ⟨x, p, ⟨k, rfl⟩, hp, e⟩
    refine ⟨k, p, hp, ?_⟩
    have h : (2 * k + 1) ^ 2 = 4 * k * (k + 1) + 1 := by ring
    have h' : 2 * k * (k + 1) * 2 = 4 * k * (k + 1) := by ring
    rw [h] at e
    omega
  · rintro ⟨k, p, hp, e⟩
    refine ⟨2 * k + 1, p, ⟨k, rfl⟩, hp, ?_⟩
    have h : (2 * k + 1) ^ 2 = 4 * k * (k + 1) + 1 := by ring
    have h' : 2 * k * (k + 1) * 2 = 4 * k * (k + 1) := by ring
    rw [h]
    omega

/-- `8n + 3` is never a square, so no algebraic factorisation blocks it, unlike `p + x²`. -/
theorem not_square_8n3 (n : ℕ) : ¬ IsSquare (8 * n + 3) := by
  rintro ⟨r, hr⟩
  have h : (r * r) % 8 = 0 ∨ (r * r) % 8 = 1 ∨ (r * r) % 8 = 4 := by
    have : r % 8 < 8 := Nat.mod_lt _ (by norm_num)
    rw [Nat.mul_mod]
    interval_cases (r % 8) <;> simp
  omega

/-- Finite search, `x` odd below the bound. -/
def euB (n : ℕ) : Bool :=
  (List.range 40).any fun k =>
    decide (2 * k * (k + 1) < 4 * n + 1) && primeB (4 * n + 1 - 2 * k * (k + 1))

theorem euB_sound {n : ℕ} (h : euB n = true) : IsEuler (8 * n + 3) := by
  rw [isEuler_iff_triangular]
  simp only [euB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨k, _, h1, h2⟩ := h
  exact ⟨k, _, primeB_sound h2, by omega⟩

/-- A small range, for vacuity and a smoke test only. Vantieghem on Conjecture 68 gives a table of
record ratios and says no value above 1.57847 is found for `N ≤ 10⁹`. The page states this as a bound
on the ratio, so it is not cited here as a verification of the decomposition. KNOWN. -/
theorem euler_le_1000 : ∀ n, 1 ≤ n → n ≤ 1000 → IsEuler (8 * n + 3) := by
  have h : (List.range 1001).all (fun n => n == 0 || euB n) = true := by decide +kernel
  intro n h1 h2
  have := List.all_eq_true.mp h n (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h0 | h0
  · omega
  · exact euB_sound h0

attribute [local instance] Classical.propDecidable in
/-- Number of `n ≤ X`, `n ≥ 1`, with no representation. -/
noncomputable def euExc (X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter fun n => ¬ IsEuler (8 * n + 3)).card

/-- `euExc X` is a count of at most `X` integers, so the truncated `X - euExc X` in the density route
reads as a count. PROVED, U-1618. -/
theorem euExc_le (X : ℕ) : euExc X ≤ X := by
  classical
  unfold euExc
  refine (Finset.card_filter_le _ _).trans ?_
  simp

/-- The sealed statement says exactly that the exception count is always zero. -/
theorem statement_iff_euExc : Euler8n3Statement ↔ ∀ X, euExc X = 0 := by
  classical
  constructor
  · intro h X
    unfold euExc
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro n hn
    simpa using h n (Finset.mem_Icc.mp hn).1
  · intro h n hn
    have := h n
    unfold euExc at this
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at this
    simpa using this (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)

/-- ROUTE, sorry, NOT PROVED. The smallest step: a positive proportion of `8n + 3` are represented.
Expected by a second moment over `x`, as in Hua's sum of a prime and a square; not searched as a
named theorem for this restricted form. Weaker than the problem. -/
theorem route_euler_positive_density :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in Filter.atTop, c * X ≤ ((X - euExc X : ℕ) : ℝ) := by
  sorry

/-- ROUTE, sorry, NOT PROVED. Almost all `8n + 3` are represented, the analogue for `2p + x²` of
Davenport and Heilbronn 1937 for `p + x²`. Weaker than the problem. -/
theorem route_euler_almost_all :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in Filter.atTop, (euExc X : ℝ) ≤ ε * X := by
  sorry

/-! ### 2. Powerful number as a prime plus a powerful number -/

/-- `n` is powerful: every prime factor divides it at least twice. `1` counts. `0 < n` is built in, so
`0` is excluded, though the plain condition holds for it. Harmless for `PowerfulPrimeStatement`: it
has `1 < N`, and a summand `M = 0` would make `N` prime, which is not powerful. -/
def Powerful (n : ℕ) : Prop := 0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- **OPEN, sealed.** Every powerful `N > 1` is a prime plus a powerful number. -/
def PowerfulPrimeStatement : Prop :=
  ∀ N : ℕ, Powerful N → 1 < N → ∃ p M : ℕ, p.Prime ∧ Powerful M ∧ N = p + M

theorem powerful_one : Powerful 1 :=
  ⟨one_pos, fun p hp h => absurd (Nat.dvd_one.mp h) hp.ne_one⟩

theorem powerful_sq {k : ℕ} (hk : 0 < k) : Powerful (k ^ 2) :=
  ⟨by positivity, fun _ hp h => pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow h) 2⟩

theorem powerful_eight_sq {a : ℕ} (ha : 0 < a) : Powerful (8 * a ^ 2) := by
  refine ⟨by positivity, fun p hp h => ?_⟩
  rcases (Nat.Prime.dvd_mul hp).mp h with h8 | h2
  · have : p ∣ 2 ^ 3 := by simpa using h8
    have h2' := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this)
    subst h2'
    exact ⟨2 * a ^ 2, by ring⟩
  · exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow h2) 2) 8

theorem not_powerful_six : ¬ Powerful 6 := by
  rintro ⟨_, h⟩
  exact absurd (h 2 Nat.prime_two (by norm_num)) (by norm_num)

theorem not_powerful_two : ¬ Powerful 2 := by
  rintro ⟨_, h⟩
  exact absurd (h 2 Nat.prime_two (by norm_num)) (by norm_num)

/-- Vacuity: `4 = 3 + 1`, `9 = 5 + 4`. -/
theorem rep_four : ∃ p M : ℕ, p.Prime ∧ Powerful M ∧ 4 = p + M :=
  ⟨3, 1, Nat.prime_three, powerful_one, rfl⟩

theorem rep_nine : ∃ p M : ℕ, p.Prime ∧ Powerful M ∧ 9 = p + M :=
  ⟨5, 4, by norm_num, by simpa using powerful_sq (k := 2) (by norm_num), rfl⟩

/-- If `1` were excluded, `4` would fail, so the statement needs `1` powerful. -/
theorem not_rep_four_of_one_excluded :
    ¬ ∃ p M : ℕ, p.Prime ∧ Powerful M ∧ 1 < M ∧ 4 = p + M := by
  rintro ⟨p, M, hp, hM, h1, e⟩
  have := hp.two_le
  have hM2 : M = 2 := by omega
  subst hM2
  exact not_powerful_two hM

/-- The square route: if `2m - 1` is prime then `m² = (2m - 1) + (m - 1)²`. PROVED, elementary. -/
theorem sq_of_prime {m : ℕ} (hm : 2 ≤ m) (hp : (2 * m - 1).Prime) :
    ∃ p M : ℕ, p.Prime ∧ Powerful M ∧ m ^ 2 = p + M := by
  refine ⟨_, (m - 1) ^ 2, hp, powerful_sq (by omega), ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have h2 : k + 1 - 1 = k := by omega
  rw [h1, h2]
  ring

/-- With square `M`, `m²` is `p + M` only for `p = 2m - 1`, so the square route is exhausted when
`2m - 1` is composite and a nonsquare `M` is forced. PROVED, elementary. -/
theorem sq_route_exhausted {m p a : ℕ} (hp : p.Prime) (e : m ^ 2 = p + a ^ 2) : p = 2 * m - 1 := by
  have hp2 := hp.two_le
  have ham : a < m := by
    by_contra hc
    have : m ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left (not_lt.mp hc) 2
    omega
  obtain ⟨d, rfl⟩ : ∃ d, m = a + d := ⟨m - a, by omega⟩
  have hd : 0 < d := by omega
  have hpd : p = d * (2 * a + d) := by
    have : (a + d) ^ 2 = d * (2 * a + d) + a ^ 2 := by ring
    omega
  rcases (Nat.prime_mul_iff.mp (hpd ▸ hp)) with ⟨hd2, h⟩ | ⟨_, h⟩
  · have := hd2.two_le
    omega
  · subst h
    omega


mutual
def pellM : ℕ → ℕ
| 0 => 5
| (n+1) => 3 * pellM n + 8 * pellA n

def pellA : ℕ → ℕ
| 0 => 1
| (n+1) => pellM n + 3 * pellA n
end

def state (n : ℕ) : ℕ × ℕ := (pellM n % 5, pellA n % 5)

lemma state_succ (n : ℕ) : state (n + 1) = ((3 * (state n).1 + 8 * (state n).2) % 5, ((state n).1 + 3 * (state n).2) % 5) := by
  dsimp [state]
  have h1 : pellM (n + 1) = 3 * pellM n + 8 * pellA n := rfl
  have h2 : pellA (n + 1) = pellM n + 3 * pellA n := rfl
  rw [h1, h2]
  ext <;> dsimp <;> omega

lemma state_6n (n : ℕ) : state (6 * n) = (0, 1) := by
  induction' n with n ih
  · rfl
  · have h1 : 6 * (n + 1) = 6 * n + 6 := by ring
    rw [h1]
    have step1 : state (6 * n + 1) = (3, 3) := by rw [state_succ, ih]; rfl
    have step2 : state (6 * n + 2) = (3, 2) := by rw [state_succ, step1]; rfl
    have step3 : state (6 * n + 3) = (0, 4) := by rw [state_succ, step2]; rfl
    have step4 : state (6 * n + 4) = (2, 2) := by rw [state_succ, step3]; rfl
    have step5 : state (6 * n + 5) = (2, 3) := by rw [state_succ, step4]; rfl
    have step6 : state (6 * n + 6) = (0, 1) := by rw [state_succ, step5]; rfl
    exact step6

lemma state_6n_1 (n : ℕ) : state (6 * n + 1) = (3, 3) := by
  have step1 : state (6 * n + 1) = (3, 3) := by rw [state_succ, state_6n]; rfl
  exact step1

lemma pell_eq (n : ℕ) : (pellM n)^2 = 17 + 8 * (pellA n)^2 := by
  induction' n with n ih
  · rfl
  · have h1 : pellM (n+1) = 3 * pellM n + 8 * pellA n := rfl
    have h2 : pellA (n+1) = pellM n + 3 * pellA n := rfl
    rw [h1, h2]
    nlinarith

lemma div_5_2m_1 (n : ℕ) : (2 * pellM (6 * n + 1) - 1) % 5 = 0 := by
  have h : pellM (6 * n + 1) % 5 = 3 := by
    have h2 := state_6n_1 n
    exact congrArg Prod.fst h2
  omega

lemma pellM_ge (n : ℕ) : pellM n ≥ 5 := by
  induction' n with n ih
  · rfl
  · have h1 : pellM (n+1) = 3 * pellM n + 8 * pellA n := rfl
    rw [h1]
    omega

lemma pellM_ge_11 (n : ℕ) : pellM (n + 1) ≥ 23 := by
  induction' n with n ih
  · rfl
  · have h1 : pellM (n+2) = 3 * pellM (n+1) + 8 * pellA (n+1) := rfl
    rw [h1]
    omega

lemma not_prime_2m_1 (n : ℕ) : ¬ (2 * pellM (6 * n + 1) - 1).Prime := by
  intro h
  have h1 := div_5_2m_1 n
  have h2 : 5 ∣ 2 * pellM (6 * n + 1) - 1 := Nat.dvd_of_mod_eq_zero h1
  have h3 : 2 * pellM (6 * n + 1) - 1 = 5 := by
    have tmp := (Nat.prime_dvd_prime_iff_eq (by norm_num) h).mp h2
    exact tmp.symm
  have h4 : pellM (6 * n + 1) ≥ 23 := by
    have := pellM_ge_11 (6 * n)
    exact this
  omega

lemma pellA_ge_1 (n : ℕ) : pellA n ≥ 1 := by
  induction' n with n ih
  · rfl
  · have h2 : pellA (n+1) = pellM n + 3 * pellA n := rfl
    rw [h2]
    omega

lemma pellM_mono (n : ℕ) : pellM n < pellM (n + 1) := by
  have h1 : pellM (n+1) = 3 * pellM n + 8 * pellA n := rfl
  rw [h1]
  have hm := pellM_ge n
  omega

lemma pellM_ge_n (n : ℕ) : pellM n ≥ n := by
  induction' n with n ih
  · omega
  · have h := pellM_mono n
    omega

/-- ROUTE, PROVED. Infinitely many squares with `2m - 1` composite still work, through `M = 8 a²`:
the Pell family `m² - 8 a² = 17`, `(5, 1) ↦ (3m + 8a, m + 3a)`, plus a periodicity mod a small prime
to force `2m - 1` composite. -/
theorem route_powerful_nonsquare_family :
    ∀ K : ℕ, ∃ m > K, ¬ (2 * m - 1).Prime ∧ ∃ p a : ℕ, p.Prime ∧ 0 < a ∧ m ^ 2 = p + 8 * a ^ 2 := by
  intro K
  let N := K
  use pellM (6 * N + 1)
  constructor
  · have h1 := pellM_ge_n (6 * N + 1)
    omega
  · constructor
    · exact not_prime_2m_1 N
    · use 17, pellA (6 * N + 1)
      constructor
      · norm_num
      · constructor
        · have := pellA_ge_1 (6 * N + 1)
          omega
        · have := pell_eq (6 * N + 1)
          omega

end LeanLab.OpenProblems.State1612

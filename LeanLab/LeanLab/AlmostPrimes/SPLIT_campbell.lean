/-
Split of `campbell` in `AlmostPrimes/Statements.lean` into four leaves, following the
three-range structure recorded in `AlmostPrimes/PROGRESS.md` for that statement:

* `2 ≤ N ≤ N₀ = 117465180365547648498934439`: the short-interval argument on top of the
  maximal prime gap table input;
* `N₀ < N < 10^132`: the finite verification of a positive sieve sum on the middle range;
* `N ≥ 10^132`: the explicit sieve, which produces two positive summands every prime factor
  of which exceeds `N^(2/33)`;
* a positive integer all of whose prime factors exceed `N^(2/33)` has at most 16 prime
  factors with multiplicity, hence `Ω(ab) ≤ 16 + 16 ≤ 33` for two such summands.

Each leaf is weaker than the target and none of them restates it. `campbell_split` is proved
from the four leaves with no `sorry` and does not use `campbell`.
-/
import LeanLab.AlmostPrimes.Statements

namespace LeanLab.AlmostPrimes

/-- LEAF 1, the lower range: every `2 ≤ N ≤ N₀` is a sum of two positive integers whose
product has at most 33 prime factors with multiplicity. This is the short-interval step with
the gap table input, applied below `N₀`. -/
theorem leaf_small_range : ∀ N : ℕ, 2 ≤ N → N ≤ 117465180365547648498934439 →
    TwoAlmostPrimes 33 N := by
  sorry

/-- LEAF 2, the middle range: every `N₀ < N < 10^132` is a sum of two positive integers whose
product has at most 33 prime factors with multiplicity. This is the finite verification of a
positive sieve sum on the middle range, converted into the sum of two almost primes. -/
theorem leaf_middle_range : ∀ N : ℕ, 117465180365547648498934439 < N → N < 10 ^ 132 →
    TwoAlmostPrimes 33 N := by
  sorry

/-- LEAF 3, the upper range, sieve output: for every `N ≥ 10^132` there are positive `a, b` with
`N = a + b` and every prime factor of `a` and of `b` strictly larger than `N^(2/33)`. This is
what the explicit sieve produces at `z = N^(2/33)`; it does not itself mention `TwoAlmostPrimes`. -/
theorem leaf_large_sieve_output : ∀ N : ℕ, 10 ^ 132 ≤ N → ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
    N = a + b ∧ (∀ p : ℕ, p.Prime → p ∣ a → (N : ℝ) ^ ((2 : ℝ) / 33) < (p : ℝ)) ∧
      (∀ p : ℕ, p.Prime → p ∣ b → (N : ℝ) ^ ((2 : ℝ) / 33) < (p : ℝ)) := by
  sorry

/-! ### Private helpers for LEAF 4

If every entry of a list of naturals is at least a real constant `C ≥ 0`, the
`length`-th power of `C` is at most the product of the list; if the entries are
strictly larger and the list is nonempty, the inequality is strict. -/
private theorem list_prod_rpow_le {C : ℝ} (hC : 0 ≤ C) (L : List ℕ)
    (h : ∀ x ∈ L, C ≤ (x : ℝ)) : C ^ L.length ≤ ((L.prod : ℕ) : ℝ) := by
  induction L with
  | nil => simp
  | cons x t ih =>
    have hx : C ≤ (x : ℝ) := h x (by simp)
    have ht : ∀ y ∈ t, C ≤ (y : ℝ) := fun y hy => h y (by simp [hy])
    have ih' := ih ht
    have hxp : (0 : ℝ) ≤ (x : ℝ) := le_trans hC hx
    calc C ^ (x :: t).length = C ^ t.length * C := by simp [pow_succ]
      _ = C * C ^ t.length := by ring
      _ ≤ (x : ℝ) * ((t.prod : ℕ) : ℝ) := mul_le_mul hx ih' (pow_nonneg hC _) hxp
      _ = (((x :: t).prod : ℕ) : ℝ) := by simp [List.prod_cons, Nat.cast_mul]

private theorem list_prod_rpow_lt {C : ℝ} (hC : 0 < C) (L : List ℕ) (hne : L ≠ [])
    (h : ∀ x ∈ L, C < (x : ℝ)) : C ^ L.length < ((L.prod : ℕ) : ℝ) := by
  rcases L with - | ⟨x, t⟩
  · exact absurd rfl hne
  cases t with
  | nil =>
    have hx : C < (x : ℝ) := h x (by simp)
    simpa using hx
  | cons y t' =>
    have hx : C < (x : ℝ) := h x (by simp)
    have hle : C ^ (y :: t').length ≤ (((y :: t').prod : ℕ) : ℝ) :=
      list_prod_rpow_le (le_of_lt hC) (y :: t') fun z hz => le_of_lt (h z (by simp [hz]))
    have hpos : (0 : ℝ) < (x : ℝ) := lt_trans hC hx
    calc C ^ (x :: y :: t').length = C * C ^ (y :: t').length := by
          simp [pow_succ]; ring
      _ < (x : ℝ) * C ^ (y :: t').length := mul_lt_mul_of_pos_right hx (pow_pos hC _)
      _ ≤ (x : ℝ) * (((y :: t').prod : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hle (le_of_lt hpos)
      _ = (((x :: y :: t').prod : ℕ) : ℝ) := by simp [List.prod_cons, Nat.cast_mul]

/-- LEAF 4, the counting step: a positive `a ≤ N` all of whose prime factors exceed `N^(2/33)`
has at most 16 prime factors with multiplicity, since `a` is then larger than `N^(2/33)` to the
power `Ω a` while `a ≤ N = (N^(2/33))^(33/2)` and `33/2 = 16.5`. -/
theorem leaf_omega_bound_of_large_prime_factors : ∀ (N a : ℕ), 10 ^ 132 ≤ N → 0 < a → a ≤ N →
    (∀ p : ℕ, p.Prime → p ∣ a → (N : ℝ) ^ ((2 : ℝ) / 33) < (p : ℝ)) → bigOmega a ≤ 16 := by
  intro N a hN ha hale hfac
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  set C : ℝ := (N : ℝ) ^ ((2 : ℝ) / 33) with hCdef
  have hCpos : (0 : ℝ) < C := by
    rw [hCdef]; exact Real.rpow_pos_of_pos hNpos _
  have hC1 : (1 : ℝ) < C := by
    have h0 : (N : ℝ) ^ (0 : ℝ) < (N : ℝ) ^ ((2 : ℝ) / 33) :=
      Real.rpow_lt_rpow_of_exponent_lt hN1 (by norm_num)
    simpa [hCdef] using h0
  by_contra hcon
  have h17 : 17 ≤ bigOmega a := by omega
  have hane : a ≠ 0 := by omega
  have hLne : a.primeFactorsList ≠ [] := by
    intro hnil
    have h0 : bigOmega a = 0 := by simp [bigOmega, hnil]
    omega
  have hbound : ∀ x ∈ a.primeFactorsList, C < (x : ℝ) := fun x hx =>
    hfac x (Nat.prime_of_mem_primeFactorsList hx) (Nat.dvd_of_mem_primeFactorsList hx)
  have hstrict : C ^ a.primeFactorsList.length < ((a.primeFactorsList.prod : ℕ) : ℝ) :=
    list_prod_rpow_lt hCpos _ hLne hbound
  rw [Nat.prod_primeFactorsList hane] at hstrict
  have hlen : a.primeFactorsList.length = bigOmega a := rfl
  rw [hlen] at hstrict
  have hpow : C ^ 17 ≤ C ^ bigOmega a := pow_le_pow_right₀ (le_of_lt hC1) h17
  have hlt_a : C ^ 17 < (a : ℝ) := lt_of_le_of_lt hpow hstrict
  have hrpow : C ^ 17 = (N : ℝ) ^ ((34 : ℝ) / 33) := by
    rw [hCdef, ← Real.rpow_natCast ((N : ℝ) ^ ((2 : ℝ) / 33)) 17,
      ← Real.rpow_mul (le_of_lt hNpos)]
    congr 1
    norm_num
  have hltN : (N : ℝ) < (N : ℝ) ^ ((34 : ℝ) / 33) := by
    have h := Real.rpow_lt_rpow_of_exponent_lt hN1 (by norm_num : (1 : ℝ) < (34 : ℝ) / 33)
    simpa using h
  have hale' : (a : ℝ) ≤ (N : ℝ) := by exact_mod_cast hale
  have hbig : (N : ℝ) < (a : ℝ) := by
    calc (N : ℝ) < (N : ℝ) ^ ((34 : ℝ) / 33) := hltN
      _ = C ^ 17 := hrpow.symm
      _ < (a : ℝ) := hlt_a
  linarith

/-- Private helper with a full proof: `Ω` is additive on a product of positive integers. -/
private theorem bigOmega_mul_add {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    bigOmega (a * b) = bigOmega a + bigOmega b := by
  simp only [bigOmega_eq_cardFactors]
  exact ArithmeticFunction.cardFactors_mul ha hb

/-- The target statement, assembled from the four leaves. -/
theorem campbell_split : ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 33 N := by
  intro N h2
  rcases Nat.lt_or_ge 117465180365547648498934439 N with hmid | hlow
  · rcases Nat.lt_or_ge N (10 ^ 132) with hlt | hge
    · exact leaf_middle_range N hmid hlt
    · obtain ⟨a, b, ha, hb, hN, hpa, hpb⟩ := leaf_large_sieve_output N hge
      have hale : a ≤ N := by omega
      have hble : b ≤ N := by omega
      have hoa : bigOmega a ≤ 16 := leaf_omega_bound_of_large_prime_factors N a hge ha hale hpa
      have hob : bigOmega b ≤ 16 := leaf_omega_bound_of_large_prime_factors N b hge hb hble hpb
      refine ⟨a, b, ha, hb, hN, ?_⟩
      rw [bigOmega_mul_add ha.ne' hb.ne']
      omega
  · exact leaf_small_range N h2 hlow

#print axioms campbell_split

end LeanLab.AlmostPrimes

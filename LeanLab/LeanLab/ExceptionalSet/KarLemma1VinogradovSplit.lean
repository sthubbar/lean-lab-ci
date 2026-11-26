/-
Split of the leaf `leaf_vinogradov_recursion` of `KarLemma1Recursion`, Vinogradov's recursive
inequality, the step of his mean value theorem as Karacuba 1971 cites it for Lemma 1, p. 243,
his reference [2].

Notation as in `KarLemma1Recursion`: `N = n(n+1)/2`, `k = [n(n+1)/4 + 1]`, `b = n m + k`,
`J_s(P)` the count of pairs of `s`-tuples in `[1, P]` with equal power sums of orders `1..n`,
`P1 = [P^(1-1/n)]`, `e = 2n + 2b/n - (n+1)/2`.

Vinogradov's proof. Fix a prime `p` with `p ≤ P^(1/n) < 2p`, the prime of [2] near `P^(1/n)`.
Sort the solutions of the system for `J_(b+n)(P)` into classes by the residues mod `p` of the
first `n` unknowns of each side:
* `G`, both sides well spaced: the first `n` unknowns pairwise incongruent mod `p`;
* `B`, neither side well spaced;
* `M`, the mixed classes.
Then
* `J_(b+n)(P) = G + B + M`, proved, `J_eq_classes`;
* `leaf_mixed_classes`: `M ≤ G + B`, Cauchy and Schwarz in counting form, proved;
* LEAF `leaf_well_spaced`: `G ≤ V`, the well spaced case, after the substitution
  `x = u + p z` the congruences are counted by the lemma of Linnik and Vinogradov on systems of
  congruences with pairwise incongruent unknowns, and the remaining `b` unknowns run over
  `[1, P/p]`;
* LEAF `leaf_not_well_spaced`: `B ≤ V`, the non well spaced case;
here `V = (20n)^N / 4 · p^(2b) · P^(2n - (n+1)/2) · J_b([P/p])`;
* LEAF `leaf_length_change`: `p^(2b) J_b([P/p]) ≤ P^(2b/n) J_b(P1)`, the passage from
  Vinogradov's length `P/p` to the length `P1` used in the lab's form of the recursion;
* the existence of `p` when `P^(1/n) ≥ 2`, proved from Bertrand's postulate,
  `exists_vinogradov_prime`;
* the short root regime `P^(1/n) < 2`, where no such prime exists, by an elementary route:
  LEAF `leaf_extra_unknowns`, `J_(s+t)(P) ≤ P^(2t) J_s(P)`, MEDIUM; LEAF `leaf_block_split`,
  `J_s(P) ≤ 9^s J_s(P1)`, MEDIUM; and the arithmetic `short_root_arith`, proved, which uses
  `(20n)^(m+1) ≤ P < 2^n` to bound `9^b ≤ (20n)^N`;
* the combining arithmetic `J ≤ 2(G + B) ≤ 4V ≤ (20n)^N P^e J_b(P1)`, proved.
The assembly `leaf_vinogradov_recursion_split` has exactly the type of the leaf, by a twin.

QUESTION. The constants of the class leaves and the exact form of Vinogradov's lemma were not
checked against a copy of [2]; `papers/` holds no Vinogradov book. The leaf
`leaf_length_change` is the doubtful one: it is heuristically true, since `J_b(X)` behaves
like `X^(2b-N)` and `p^N ≤ P^(N/n)`, but it is not a step of Vinogradov's proof; it isolates
the loss between the lab's form with `P1` and Vinogradov's form with `P/p`, which can be up to
a factor `4^b` if handled crudely.

AI wrote the Lean code.
-/
import LeanLab.ExceptionalSet.KarLemma1Recursion

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit.VinogradovSplit

open LeanLab.ExceptionalSet.U1539 LeanLab.ExceptionalSet.U1539.KaracubaSplit

open Classical

/-- The lab's count `J_s(P)` of pairs of `s`-tuples in `[1, P]` with equal power sums of
orders `1, ..., n`, literally the sums of `KarLemma1Recursion`; Karacuba 1971 p. 243. -/
noncomputable def vJ (n s P : ℕ) : ℝ :=
  ∑ x : Fin s → Fin P, ∑ y : Fin s → Fin P,
    (if (∀ j : Fin n,
        ∑ i : Fin s, (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
          = ∑ i : Fin s, (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
      then (1 : ℝ) else 0)

/-- The number of solutions counted by `J_s(P)` that lie in the class `c`, for the sorting of
solutions into classes in Vinogradov's proof of the recursive inequality, [2] of Karacuba 1971. -/
noncomputable def classCount (n s P : ℕ) (c : (Fin s → Fin P) → (Fin s → Fin P) → Prop) : ℝ :=
  ∑ x : Fin s → Fin P, ∑ y : Fin s → Fin P,
    (if (∀ j : Fin n,
        ∑ i : Fin s, (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
          = ∑ i : Fin s, (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)) ∧ c x y
      then (1 : ℝ) else 0)

/-- Vinogradov's well spaced condition: the first `n` unknowns of the tuple, as integers in
`[1, P]`, are pairwise incongruent modulo the prime `p`. -/
def wellSpaced (n p s P : ℕ) (x : Fin s → Fin P) : Prop :=
  ∀ i j : Fin s, i.val < n → j.val < n → i ≠ j →
    ¬ ((x i).val + 1) ≡ ((x j).val + 1) [MOD p]

/-- The decomposition of `J_s(P)` into the three classes: both sides well spaced, neither,
and mixed. Proved. -/
theorem J_eq_classes (n p s P : ℕ) :
    vJ n s P = classCount n s P (fun x y => wellSpaced n p s P x ∧ wellSpaced n p s P y)
      + classCount n s P (fun x y => ¬ wellSpaced n p s P x ∧ ¬ wellSpaced n p s P y)
      + classCount n s P (fun x y => ¬ (wellSpaced n p s P x ↔ wellSpaced n p s P y)) := by
  unfold vJ classCount
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases he : (∀ j : Fin n,
        ∑ i : Fin s, (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
          = ∑ i : Fin s, (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)) <;>
  by_cases hx : wellSpaced n p s P x <;> by_cases hy : wellSpaced n p s P y <;>
  simp [he, hx, hy]

/-- A sum `Σ_x Σ_y [φ x = φ y] f x f y` is nonnegative: it is the sum over the fibres of `φ`
of the squares of the fibre sums of `f`. Proved; the counting form of Cauchy and Schwarz. -/
theorem fibre_sum_nonneg {α β : Type*} [Fintype α] (φ : α → β) (f : α → ℝ) :
    0 ≤ ∑ x, ∑ y, (if φ x = φ y then f x * f y else 0) := by
  set F : β → ℝ := fun v => ∑ y, if φ y = v then f y else 0 with hF
  have h1 : ∀ x, ∑ y, (if φ x = φ y then f x * f y else 0) = f x * F (φ x) := by
    intro x
    rw [hF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : φ x = φ y
    · simp [h]
    · simp [h, Ne.symm h]
  simp_rw [h1]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image φ)
    (g := φ) (fun x _ => Finset.mem_image_of_mem φ (Finset.mem_univ x))]
  apply Finset.sum_nonneg
  intro v _
  have h2 : ∑ x ∈ Finset.univ.filter (fun x => φ x = v), f x * F (φ x)
      = F v * F v := by
    rw [Finset.sum_congr rfl (g := fun x => f x * F v) (fun x hx => by
      rw [(Finset.mem_filter.mp hx).2])]
    rw [← Finset.sum_mul, hF, Finset.sum_filter]
  rw [h2]; exact mul_self_nonneg _

/-- Vinogradov's recursive inequality [2], cited by Karacuba 1971 p. 243, the mixed
classes, proved. Writing `J_(b+n)(P)` as the integral over the unit cube of `|S|^(2(b+n))`
and splitting the `n`-fold product of the first unknowns into its well spaced part and the
rest, the cross terms are bounded by Cauchy and Schwarz: `M ≤ 2 sqrt(G B) ≤ G + B`. -/
theorem leaf_mixed_classes (n p s P : ℕ) :
    classCount n s P (fun x y => ¬ (wellSpaced n p s P x ↔ wellSpaced n p s P y))
      ≤ classCount n s P (fun x y => wellSpaced n p s P x ∧ wellSpaced n p s P y)
        + classCount n s P (fun x y => ¬ wellSpaced n p s P x ∧ ¬ wellSpaced n p s P y) := by
  set φ : (Fin s → Fin P) → (Fin n → ℝ) :=
    fun x j => ∑ i : Fin s, (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1) with hφ
  set f : (Fin s → Fin P) → ℝ := fun x => if wellSpaced n p s P x then 1 else -1 with hf
  have key : classCount n s P (fun x y => wellSpaced n p s P x ∧ wellSpaced n p s P y)
        + classCount n s P (fun x y => ¬ wellSpaced n p s P x ∧ ¬ wellSpaced n p s P y)
        - classCount n s P (fun x y => ¬ (wellSpaced n p s P x ↔ wellSpaced n p s P y))
      = ∑ x, ∑ y, (if φ x = φ y then f x * f y else 0) := by
    unfold classCount
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases he : (∀ j : Fin n,
        ∑ i : Fin s, (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
          = ∑ i : Fin s, (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
    · have hq : φ x = φ y := funext he
      by_cases hx : wellSpaced n p s P x <;> by_cases hy : wellSpaced n p s P y <;>
        simp only [eq_true he, true_and] <;> simp [hq, hx, hy, hf]
    · have hq : φ x ≠ φ y := fun h => he (fun j => congrFun h j)
      simp only [eq_false he, false_and] <;> simp [hq]
  have h0 : 0 ≤ ∑ x, ∑ y, (if φ x = φ y then f x * f y else 0) := by
    convert fibre_sum_nonneg φ f
  rw [← key] at h0
  exact sub_nonneg.mp h0

/-- LEAF: Vinogradov's recursive inequality [2], cited by Karacuba 1971 p. 243, the well
spaced case. HARD. For a prime `p` with `p ≤ P^(1/n) < 2p`, the solutions of the system for
`J_(b+n)(P)`, `b = n m + k`, whose first `n` unknowns on both sides are pairwise incongruent
mod `p` number at most `(20n)^N / 4 · p^(2b) · P^(2n - (n+1)/2) · J_b([P/p])`: Hoelder over
the residue classes of the last `b` unknowns gives the factor `p^(2b)`, the substitution
`x = u + p z` and the binomial theorem reduce the remaining equations to a system of
congruences in the well spaced unknowns, counted by the Linnik and Vinogradov lemma. -/
theorem leaf_well_spaced :
    ∀ n : ℕ, 12 ≤ n → ∀ m : ℕ, 1 ≤ m → ∀ P : ℕ, (20 * n : ℝ) ^ (m + 1) ≤ P →
    ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (P : ℝ) ^ (1 / (n : ℝ)) →
      (P : ℝ) ^ (1 / (n : ℝ)) < 2 * p →
      classCount n (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) P
          (fun x y => wellSpaced n p _ P x ∧ wellSpaced n p _ P y)
        ≤ (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2) / 4 *
            (p : ℝ) ^ (2 * (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊))) *
            (P : ℝ) ^ (2 * (n : ℝ) - ((n : ℝ) + 1) / 2) *
            vJ n (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) (P / p) := by
  sorry

/-- LEAF: Vinogradov's recursive inequality [2], cited by Karacuba 1971 p. 243, the non well
spaced case. HARD. For a prime `p` with `p ≤ P^(1/n) < 2p`, the solutions whose first `n`
unknowns on neither side are pairwise incongruent mod `p` number at most the same bound
`(20n)^N / 4 · p^(2b) · P^(2n - (n+1)/2) · J_b([P/p])`: a coincidence `x_i ≡ x_j mod p` saves
a factor `p` in the count of the first `n` unknowns on each side. -/
theorem leaf_not_well_spaced :
    ∀ n : ℕ, 12 ≤ n → ∀ m : ℕ, 1 ≤ m → ∀ P : ℕ, (20 * n : ℝ) ^ (m + 1) ≤ P →
    ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (P : ℝ) ^ (1 / (n : ℝ)) →
      (P : ℝ) ^ (1 / (n : ℝ)) < 2 * p →
      classCount n (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) P
          (fun x y => ¬ wellSpaced n p _ P x ∧ ¬ wellSpaced n p _ P y)
        ≤ (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2) / 4 *
            (p : ℝ) ^ (2 * (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊))) *
            (P : ℝ) ^ (2 * (n : ℝ) - ((n : ℝ) + 1) / 2) *
            vJ n (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) (P / p) := by
  sorry

/-- LEAF: the passage from Vinogradov's length `P/p` in [2] to the length `P1 = [P^(1-1/n)]`
of the lab's form of the recursion for Karacuba 1971 Lemma 1, p. 243. HARD, QUESTION.
For a prime `p` with `p ≤ P^(1/n) < 2p`: `p^(2b) J_b([P/p]) ≤ P^(2b/n) J_b(P1)`. Heuristically
`J_b(X) ≍ X^(2b-N)` for `2b ≥ N` and `p^N ≤ P^(N/n)`, but this is not a step of [2]. -/
theorem leaf_length_change :
    ∀ n : ℕ, 12 ≤ n → ∀ m : ℕ, 1 ≤ m → ∀ P : ℕ, (20 * n : ℝ) ^ (m + 1) ≤ P →
    ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (P : ℝ) ^ (1 / (n : ℝ)) →
      (P : ℝ) ^ (1 / (n : ℝ)) < 2 * p →
      (p : ℝ) ^ (2 * (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊))) *
          vJ n (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) (P / p)
        ≤ (P : ℝ) ^ (2 * ((n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊) : ℕ) : ℝ) / n) *
          vJ n (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊))
            ⌊(P : ℝ) ^ (1 - 1 / (n : ℝ))⌋₊ := by
  sorry

/-- The prime of Vinogradov's proof exists: for `x ≥ 2` there is a prime `p` with `p ≤ x` and
`x < 2p`, by Bertrand's postulate. Proved. -/
theorem exists_vinogradov_prime (x : ℝ) (hx : 2 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ x < 2 * p := by
  have h0 : ⌊x / 2⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊x / 2⌋₊ := Nat.one_le_floor_iff _ |>.mpr (by linarith)
    omega
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul _ h0
  refine ⟨p, hp, ?_, ?_⟩
  · have h1 : ((2 * ⌊x / 2⌋₊ : ℕ) : ℝ) ≤ x := by
      push_cast
      have := Nat.floor_le (show (0 : ℝ) ≤ x / 2 by linarith)
      linarith
    have : (p : ℝ) ≤ ((2 * ⌊x / 2⌋₊ : ℕ) : ℝ) := by exact_mod_cast hle
    linarith
  · have h1 : ⌊x / 2⌋₊ + 1 ≤ p := hlt
    have h2' : x / 2 < (⌊x / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have : ((⌊x / 2⌋₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast h1
    push_cast at this
    linarith

/-- LEAF: the short root regime `P^(1/n) < 2`, where no prime `p ≤ P^(1/n)` exists and
Vinogradov's lemma [2], cited by Karacuba 1971 p. 243, does not apply; the elementary first
step. MEDIUM. Adding `t` unknowns on each side costs at most `P^(2t)`:
`J_(s+t)(P) = Σ_h r_s(h) r_t(h) ≤ r_s(0) Σ_h r_t(h) = P^(2t) J_s(P)`, since
`r_s(h) ≤ r_s(0)` by Cauchy and Schwarz. -/
theorem leaf_extra_unknowns (n s t P : ℕ) :
    vJ n (s + t) P ≤ (P : ℝ) ^ (2 * t) * vJ n s P := by
  sorry

/-- LEAF: the short root regime `P^(1/n) < 2`, outside Vinogradov's lemma [2] as cited by
Karacuba 1971 p. 243; the elementary second step. MEDIUM. If `P^(1/n) < 2` then
`P1 = [P^(1-1/n)]` satisfies `3 P1 ≥ P`, so `[1, P]` is the union of three blocks of length at
most `P1`; by Hoelder and the invariance of the system under translation, binomial theorem,
`J_s(P) ≤ 3^(2s) J_s(P1)`. -/
theorem leaf_block_split (n s P : ℕ) (hn : 1 ≤ n) (hP : 1 ≤ P)
    (hroot : (P : ℝ) ^ (1 / (n : ℝ)) < 2) :
    vJ n s P ≤ (9 : ℝ) ^ s * vJ n s ⌊(P : ℝ) ^ (1 - 1 / (n : ℝ))⌋₊ := by
  sorry

/-- The arithmetic of the short root regime: with `b = n m + k`, `(20n)^(m+1) ≤ P` and
`P^(1/n) < 2` give `9^b P^(2n) ≤ (20n)^N P^(2n + 2b/n - (n+1)/2)`, since then
`(20n)^m < 2^n`, so `81^(3nm) ≤ 8^(n^2)`, and `k ≤ n(n+1)/4 + 1`. Proved. -/
theorem short_root_arith (n m P : ℕ) (hn : 12 ≤ n) (hP : (20 * n : ℝ) ^ (m + 1) ≤ P)
    (hroot : (P : ℝ) ^ (1 / (n : ℝ)) < 2) :
    (9 : ℝ) ^ (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) * (P : ℝ) ^ (2 * n)
      ≤ (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2) *
        (P : ℝ) ^ (2 * (n : ℝ) + 2 * ((n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊) : ℕ) : ℝ) / n
              - ((n : ℝ) + 1) / 2) := by
  set K := ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ with hKdef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnr : (12 : ℝ) ≤ n := by exact_mod_cast hn
  have hKlo : ((n * (n + 1) : ℕ) : ℝ) / 4 ≤ (K : ℝ) := by
    have := Nat.lt_floor_add_one (((n * (n + 1) : ℕ) : ℝ) / 4 + 1)
    linarith
  have hKhi : (K : ℝ) ≤ ((n * (n + 1) : ℕ) : ℝ) / 4 + 1 := Nat.floor_le (by positivity)
  have hK4 : 4 * K ≤ n * (n + 1) + 4 := by
    have : ((4 * K : ℕ) : ℝ) ≤ ((n * (n + 1) + 4 : ℕ) : ℝ) := by push_cast at hKhi ⊢; linarith
    exact_mod_cast this
  have hC1 : (1 : ℝ) ≤ (20 * n : ℝ) ^ (m + 1) := one_le_pow₀ (by linarith)
  have hP1 : (1 : ℝ) ≤ P := le_trans hC1 hP
  have hP0 : (0 : ℝ) < P := by linarith
  have hPlt : (P : ℝ) < 2 ^ n := by
    have e : ((P : ℝ) ^ (1 / (n : ℝ))) ^ n = P := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le, one_div_mul_cancel hn0.ne', Real.rpow_one]
    rw [← e]
    exact pow_lt_pow_left₀ hroot (by positivity) (by omega)
  have hmN : (20 * n) ^ m < 2 ^ n := by
    have h : ((20 * n) ^ m : ℝ) ≤ (20 * n : ℝ) ^ (m + 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have : (((20 * n) ^ m : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  -- nat inequality
  have h81 : 81 ^ (n * m + K) ≤ (20 * n) ^ (n * (n + 1)) := by
    have hb : 81 ≤ 20 * n := by omega
    have hA : (81 ^ m) ≤ 2 ^ n := le_of_lt (lt_of_le_of_lt (Nat.pow_le_pow_left hb m) hmN)
    have hB : 81 ^ (3 * (n * m)) ≤ (20 * n) ^ (n * n) := by
      calc 81 ^ (3 * (n * m)) = ((81 ^ m) ^ n) ^ 3 := by ring
        _ ≤ ((2 ^ n) ^ n) ^ 3 := Nat.pow_le_pow_left (Nat.pow_le_pow_left hA n) 3
        _ = 8 ^ (n * n) := by
          rw [← pow_mul, ← pow_mul, show (8 : ℕ) = 2 ^ 3 from rfl, ← pow_mul]; congr 1; ring
        _ ≤ (20 * n) ^ (n * n) := Nat.pow_le_pow_left (by omega) _
    have hC : 81 ^ (3 * K) ≤ (20 * n) ^ (3 * K) := Nat.pow_le_pow_left hb _
    have hE : n * n + 3 * K ≤ 3 * (n * (n + 1)) := by nlinarith
    have h3 : (81 ^ (n * m + K)) ^ 3 ≤ ((20 * n) ^ (n * (n + 1))) ^ 3 := by
      calc (81 ^ (n * m + K)) ^ 3 = 81 ^ (3 * (n * m)) * 81 ^ (3 * K) := by ring
        _ ≤ (20 * n) ^ (n * n) * (20 * n) ^ (3 * K) := Nat.mul_le_mul hB hC
        _ = (20 * n) ^ (n * n + 3 * K) := by ring
        _ ≤ (20 * n) ^ (3 * (n * (n + 1))) := Nat.pow_le_pow_right (by omega) hE
        _ = ((20 * n) ^ (n * (n + 1))) ^ 3 := by ring
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h3
  have h9 : (9 : ℝ) ^ (n * m + K) ≤ (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2) := by
    have hsq : ((20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2)) ^ 2
        = (20 * n : ℝ) ^ (n * (n + 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      rw [← Real.rpow_natCast]; congr 1; push_cast; ring
    have h81r : ((9 : ℝ) ^ (n * m + K)) ^ 2 ≤ (20 * n : ℝ) ^ (n * (n + 1)) := by
      have : (((81 ^ (n * m + K) : ℕ)) : ℝ) ≤ (((20 * n) ^ (n * (n + 1)) : ℕ) : ℝ) := by
        exact_mod_cast h81
      push_cast at this
      calc ((9 : ℝ) ^ (n * m + K)) ^ 2 = (81 : ℝ) ^ (n * m + K) := by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ ≤ _ := this
    rw [← hsq] at h81r
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h81r
  have hsplit : (P : ℝ) ^ (2 * (n : ℝ) + 2 * ((n * m + K : ℕ) : ℝ) / n - ((n : ℝ) + 1) / 2)
      = (P : ℝ) ^ (2 * n) * (P : ℝ) ^ (2 * ((n * m + K : ℕ) : ℝ) / n - ((n : ℝ) + 1) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hP0]; congr 1; push_cast; ring
  have hge : (1 : ℝ) ≤ (P : ℝ) ^ (2 * ((n * m + K : ℕ) : ℝ) / n - ((n : ℝ) + 1) / 2) := by
    apply Real.one_le_rpow hP1
    have h1 : ((n : ℝ) + 1) / 2 ≤ 2 * (K : ℝ) / n := by
      rw [le_div_iff₀ hn0]; push_cast at hKlo; nlinarith
    have h2 : 2 * (K : ℝ) / n ≤ 2 * ((n * m + K : ℕ) : ℝ) / n := by
      apply div_le_div_of_nonneg_right _ hn0.le; push_cast
      have : (0 : ℝ) ≤ n * m := by positivity
      linarith
    linarith
  rw [hsplit]
  have hPn : (0 : ℝ) ≤ (P : ℝ) ^ (2 * n) := by positivity
  calc (9 : ℝ) ^ (n * m + K) * (P : ℝ) ^ (2 * n)
      ≤ (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2) * (P : ℝ) ^ (2 * n) :=
        mul_le_mul_of_nonneg_right h9 hPn
    _ ≤ (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2) * ((P : ℝ) ^ (2 * n) *
          (P : ℝ) ^ (2 * ((n * m + K : ℕ) : ℝ) / n - ((n : ℝ) + 1) / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_mul_of_one_le_right hPn hge

/-- `J_s(P) ≥ 0`. -/
theorem vJ_nonneg (n s P : ℕ) : 0 ≤ vJ n s P := by
  unfold vJ
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

/-- The short root regime of the recursion, from the two elementary leaves and the
arithmetic. -/
theorem short_root_regime (n : ℕ) (hn : 12 ≤ n) (m : ℕ) (P : ℕ)
    (hP : (20 * n : ℝ) ^ (m + 1) ≤ P) (hroot : (P : ℝ) ^ (1 / (n : ℝ)) < 2) (hP1 : 1 ≤ P) :
      vJ n (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) P
        ≤ (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2) *
            (P : ℝ) ^ (2 * (n : ℝ) + 2 * ((n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊) : ℕ) : ℝ) / n
              - ((n : ℝ) + 1) / 2) *
          vJ n (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) ⌊(P : ℝ) ^ (1 - 1 / (n : ℝ))⌋₊ := by
  set K := ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊
  have hs : n * (m + 1) + K = (n * m + K) + n := by ring
  rw [hs]
  have h1 := leaf_extra_unknowns n (n * m + K) n P
  have h2 := leaf_block_split n (n * m + K) P (by omega) hP1 hroot
  have h3 := short_root_arith n m P hn hP hroot
  have hP0 : (0 : ℝ) ≤ (P : ℝ) ^ (2 * n) := by positivity
  have hJ := vJ_nonneg n (n * m + K) ⌊(P : ℝ) ^ (1 - 1 / (n : ℝ))⌋₊
  calc vJ n (n * m + K + n) P ≤ (P : ℝ) ^ (2 * n) * vJ n (n * m + K) P := h1
    _ ≤ (P : ℝ) ^ (2 * n) * ((9 : ℝ) ^ (n * m + K) *
          vJ n (n * m + K) ⌊(P : ℝ) ^ (1 - 1 / (n : ℝ))⌋₊) :=
        mul_le_mul_of_nonneg_left h2 hP0
    _ = ((9 : ℝ) ^ (n * m + K) * (P : ℝ) ^ (2 * n)) *
          vJ n (n * m + K) ⌊(P : ℝ) ^ (1 - 1 / (n : ℝ))⌋₊ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h3 hJ

/-- The combining arithmetic: from `J = G + B + M`, `M ≤ G + B`, `G ≤ V`, `B ≤ V` and
`4V ≤ R` follows `J ≤ R`. Proved. -/
theorem combine_classes (J G B M V R : ℝ) (hJ : J = G + B + M) (hM : M ≤ G + B)
    (hG : G ≤ V) (hB : B ≤ V) (hR : 4 * V ≤ R) : J ≤ R := by
  linarith

/-- Assembly of `leaf_vinogradov_recursion` from the classes of solutions mod `p`. -/
theorem leaf_vinogradov_recursion_split :
    ∀ n : ℕ, 12 ≤ n → ∀ m : ℕ, 1 ≤ m → ∀ P : ℕ, (20 * n : ℝ) ^ (m + 1) ≤ P →
      vJ n (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) P
        ≤ (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2) *
            (P : ℝ) ^ (2 * (n : ℝ) + 2 * ((n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊) : ℕ) : ℝ) / n
              - ((n : ℝ) + 1) / 2) *
          vJ n (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) ⌊(P : ℝ) ^ (1 - 1 / (n : ℝ))⌋₊ := by
  intro n hn m hm P hP
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hC1 : (1 : ℝ) ≤ (20 * n : ℝ) ^ (m + 1) :=
    one_le_pow₀ (by have : (12 : ℝ) ≤ n := by exact_mod_cast hn
                    linarith)
  have hP1 : (1 : ℝ) ≤ P := le_trans hC1 hP
  have hP0 : (0 : ℝ) < P := by linarith
  rcases lt_or_ge ((P : ℝ) ^ (1 / (n : ℝ))) 2 with hroot | hroot
  · exact short_root_regime n hn m P hP hroot (by exact_mod_cast hP1)
  obtain ⟨p, hp, hple, hplt⟩ := exists_vinogradov_prime ((P : ℝ) ^ (1 / (n : ℝ))) hroot
  set K := ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊
  set C : ℝ := (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2)
  have hCpos : 0 ≤ C := by positivity
  refine combine_classes _ _ _ _ _ _ (J_eq_classes n p _ P) (leaf_mixed_classes n p _ P)
    (leaf_well_spaced n hn m hm P hP p hp hple hplt)
    (leaf_not_well_spaced n hn m hm P hP p hp hple hplt) ?_
  have hL := leaf_length_change n hn m hm P hP p hp hple hplt
  have hsplit : (P : ℝ) ^ (2 * (n : ℝ) + 2 * ((n * m + K : ℕ) : ℝ) / n - ((n : ℝ) + 1) / 2)
      = (P : ℝ) ^ (2 * (n : ℝ) - ((n : ℝ) + 1) / 2) *
        (P : ℝ) ^ (2 * ((n * m + K : ℕ) : ℝ) / n) := by
    rw [← Real.rpow_add hP0]; congr 1; ring
  rw [hsplit]
  have hQ : 0 ≤ (P : ℝ) ^ (2 * (n : ℝ) - ((n : ℝ) + 1) / 2) := by positivity
  calc 4 * (C / 4 * (p : ℝ) ^ (2 * (n * m + K)) *
          (P : ℝ) ^ (2 * (n : ℝ) - ((n : ℝ) + 1) / 2) * vJ n (n * m + K) (P / p))
      = C * (P : ℝ) ^ (2 * (n : ℝ) - ((n : ℝ) + 1) / 2) *
          ((p : ℝ) ^ (2 * (n * m + K)) * vJ n (n * m + K) (P / p)) := by ring
    _ ≤ C * (P : ℝ) ^ (2 * (n : ℝ) - ((n : ℝ) + 1) / 2) *
          ((P : ℝ) ^ (2 * ((n * m + K : ℕ) : ℝ) / n) *
            vJ n (n * m + K) ⌊(P : ℝ) ^ (1 - 1 / (n : ℝ))⌋₊) :=
        mul_le_mul_of_nonneg_left hL (mul_nonneg hCpos hQ)
    _ = _ := by ring

/-- Twin: the assembly has exactly the type of the leaf `leaf_vinogradov_recursion`. -/
theorem leaf_vinogradov_recursion_proved :
    type_of% @Recursion.leaf_vinogradov_recursion := leaf_vinogradov_recursion_split

end LeanLab.ExceptionalSet.U1539.KaracubaSplit.VinogradovSplit

#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.VinogradovSplit.leaf_vinogradov_recursion_proved
#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.VinogradovSplit.J_eq_classes
#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.VinogradovSplit.exists_vinogradov_prime
#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.VinogradovSplit.combine_classes
#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.VinogradovSplit.leaf_mixed_classes
#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.VinogradovSplit.fibre_sum_nonneg
#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.VinogradovSplit.short_root_arith
#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.VinogradovSplit.short_root_regime

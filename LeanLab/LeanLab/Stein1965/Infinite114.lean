/-
P0073, page 428. An unbounded prime S-sequence with certified finite prefixes.
AI wrote this Lean code for CODEX task114. Goldbach is open.
No claim here asserts that every even target is covered.
-/
import LeanLab.Stein1965.Decomp114b

namespace LeanLab.Stein1965.Infinite114

/-- Page 428: select the first successful search result using some sufficient fuel.
The fallback 0 is used only outside the proved odd-seed and even-start domain. -/
noncomputable def selected (p0 : ℕ) (B : List ℕ) (e : ℕ) : ℕ := by
  classical
  exact if h : ∃ fuel a, findNew p0 B fuel e = some a then
    Classical.choose (Classical.choose_spec h)
  else 0

/-- Page 428: the selected result is a fresh admissible prime on the continuation domain. -/
theorem selected_spec (p0 : ℕ) (B : List ℕ) (e : ℕ)
    (hseed : ∃ b ∈ B, Odd b) (he : Even e) :
    ∃ fuel, findNew p0 B fuel e = some (selected p0 B e) ∧
      (selected p0 B e).Prime ∧ p0 ≤ selected p0 B e ∧ selected p0 B e ∉ B := by
  obtain ⟨fuel, a, ha, _⟩ := Decomp114b.primeContinuation_assembled p0 B e hseed he
  have hx : ∃ fuel a, findNew p0 B fuel e = some a := ⟨fuel, a, ha⟩
  unfold selected
  rw [dite_eq_left hx]
  have hs := Classical.choose_spec (Classical.choose_spec hx)
  exact ⟨Classical.choose hx, hs, findNew_sound p0 B (Classical.choose hx) e _ hs⟩

/-- Page 428: the selector agrees with every successful finite search. -/
theorem selected_eq_of_success (p0 : ℕ) (B : List ℕ) (e fuel a : ℕ)
    (ha : findNew p0 B fuel e = some a) : selected p0 B e = a := by
  have hx : ∃ fuel a, findNew p0 B fuel e = some a := ⟨fuel, a, ha⟩
  unfold selected
  rw [dite_eq_left hx]
  exact findNew_unique p0 B (Classical.choose hx) fuel e _ a
    (Classical.choose_spec (Classical.choose_spec hx)) ha

/-- Page 428: start at 3 and 5 and repeatedly adjoin the next selected prime. -/
noncomputable def primePrefix : ℕ → List ℕ
  | 0 => [3, 5]
  | n + 1 => primePrefix n ++ [selected 3 (primePrefix n) 8]

/-- Page 428: the initial odd seed is present in every finite prefix. -/
theorem prefix_seed (n : ℕ) : 3 ∈ primePrefix n := by
  induction n with
  | zero => simp [primePrefix]
  | succ n ih => exact List.mem_append_left _ ih

/-- Page 428: every continuation adds exactly one element. -/
theorem prefix_length (n : ℕ) : (primePrefix n).length = n + 2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [primePrefix, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Page 428: every element of every unbounded prime prefix is prime and at least 3. -/
theorem prefix_primes (n : ℕ) : ∀ p ∈ primePrefix n, p.Prime ∧ 3 ≤ p := by
  induction n with
  | zero =>
    intro p hp
    simp only [primePrefix, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> norm_num
  | succ n ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ih p hp
    · have heq : p = selected 3 (primePrefix n) 8 := List.mem_singleton.mp hp
      subst p
      obtain ⟨_, _, hprime, hbound, _⟩ := selected_spec 3 (primePrefix n) 8
        ⟨3, prefix_seed n, by decide⟩ (by decide)
      exact ⟨hprime, hbound⟩

/-- Page 428: continuation never repeats an existing prime. -/
theorem prefix_nodup (n : ℕ) : (primePrefix n).Nodup := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨_, _, _, _, hfresh⟩ := selected_spec 3 (primePrefix n) 8
      ⟨3, prefix_seed n, by decide⟩ (by decide)
    simp only [primePrefix, List.nodup_append, ih, List.nodup_singleton, true_and]
    intro a ha b hb hab
    have hb' : b = selected 3 (primePrefix n) 8 := List.mem_singleton.mp hb
    subst b
    subst a
    exact hfresh ha

/-- Page 428: extending the unbounded construction retains the earlier basis. -/
theorem prefix_subset (m n : ℕ) (h : m ≤ n) : primePrefix m ⊆ primePrefix n := by
  induction n generalizing m with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact fun _ ha => ha
  | succ n ih =>
    by_cases hmn : m ≤ n
    · intro a ha
      exact List.mem_append_left _ (ih m hmn ha)
    · have hm : m = n + 1 := by omega
      subst m
      exact fun _ ha => ha

/-- Page 428: the successive new primes after the two fixed seed elements. -/
noncomputable def sequence (n : ℕ) : ℕ := selected 3 (primePrefix n) 8

/-- Page 428: each new prime is fresh at its stage and belongs to the next prefix. -/
theorem sequence_spec (n : ℕ) : (sequence n).Prime ∧ 3 ≤ sequence n ∧
    sequence n ∉ primePrefix n ∧ sequence n ∈ primePrefix (n + 1) := by
  obtain ⟨_, _, hp, hlo, hfresh⟩ := selected_spec 3 (primePrefix n) 8
    ⟨3, prefix_seed n, by decide⟩ (by decide)
  exact ⟨hp, hlo, hfresh, List.mem_append_right _ (List.mem_singleton_self _)⟩

/-- Page 428: the generated prime sequence has no repetitions, despite backtracking. -/
theorem sequence_injective : Function.Injective sequence := by
  intro i j heq
  rcases lt_trichotomy i j with hij | hij | hji
  · have hm := prefix_subset (i + 1) j (by omega) (sequence_spec i).2.2.2
    exact False.elim ((sequence_spec j).2.2.1 (heq ▸ hm))
  · exact hij
  · have hm := prefix_subset (j + 1) i (by omega) (sequence_spec j).2.2.2
    exact False.elim ((sequence_spec i).2.2.1 (heq.symm ▸ hm))

/-- Page 428: the unbounded construction generates infinitely many distinct primes. -/
theorem sequence_infinite : (Set.range sequence).Infinite := by
  exact Set.infinite_range_of_injective sequence_injective

/-- Page 428: the first new prime after seeds 3 and 5 is 7. -/
theorem sequence_zero : sequence 0 = 7 := by
  exact selected_eq_of_success 3 [3, 5] 8 3 7 (by decide +kernel)

end LeanLab.Stein1965.Infinite114

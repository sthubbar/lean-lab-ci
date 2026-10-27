/-
P0073, equations 2.1 to 2.3, pages 427 and 428.
An elementary coverage consequence of the unbounded S-algorithm.
AI wrote this Lean code for CODEX task114. Goldbach is open.
-/
import LeanLab.Stein1965.Infinite114

namespace LeanLab.Stein1965.Coverage114

open Infinite114

/-- Equation 2.2: adding basis elements preserves every existing representation. -/
theorem covered_mono (B C : List ℕ) (hsub : B ⊆ C) (e : ℕ)
    (he : covered B e = true) : covered C e = true := by
  obtain ⟨x, hx, y, hy, hxy⟩ := (covered_iff B e).mp he
  exact (covered_iff C e).mpr ⟨x, hsub hx, y, hsub hy, hxy⟩

/-- Equations 2.1 and 2.2: uncovered even targets between the fixed scan start and N. -/
def holes (B : List ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun t => 8 ≤ t ∧ Even t ∧ covered B t = false

/-- Equation 2.2: extending the basis can only remove uncovered targets. -/
theorem holes_antitone (B C : List ℕ) (hsub : B ⊆ C) (N : ℕ) :
    holes C N ⊆ holes B N := by
  intro t ht
  simp only [holes, Finset.mem_filter, Finset.mem_range] at ht ⊢
  obtain ⟨hlt, hlo, he, hfalse⟩ := ht
  refine ⟨hlt, hlo, he, ?_⟩
  apply Bool.eq_false_iff.mpr
  intro htrue
  have hc := covered_mono B C hsub t htrue
  rw [hfalse] at hc
  contradiction

/-- Page 428: any available uncovered target forces coverage progress at or below it. -/
theorem selected_progress (B : List ℕ) (N : ℕ) (hN : 8 ≤ N) (he : Even N)
    (hnot : covered B N = false) (ha : ∃ a, bestA 3 B N = some a) :
    ∃ t, 8 ≤ t ∧ t ≤ N ∧ Even t ∧ covered B t = false ∧
      covered (B ++ [selected 3 B 8]) t = true := by
  let k := (N - 8) / 2
  have hpar := Nat.even_iff.mp he
  have hstep : 8 + 2 * k = N := by dsimp [k]; omega
  obtain ⟨a, ha⟩ := ha
  have hc : covered B (8 + 2 * k) = false := hstep.symm ▸ hnot
  have ha' : bestA 3 B (8 + 2 * k) = some a := hstep.symm ▸ ha
  obtain ⟨q, hq⟩ := findNew_complete 3 B (k + 1) 8 k a (by omega) hc ha'
  have hsel : selected 3 B 8 = q := selected_eq_of_success 3 B 8 (k + 1) q hq
  obtain ⟨j, hj, hjnot, hjbest⟩ := findNew_hit 3 B (k + 1) 8 q hq
  obtain ⟨⟨_, _, b, hb, hqb⟩, _⟩ := (bestA_spec 3 B (8 + 2 * j) q).mp hjbest
  refine ⟨8 + 2 * j, by omega, by omega, ?_, hjnot, ?_⟩
  · exact ⟨4 + j, by omega⟩
  · apply (covered_iff _ _).mpr
    exact ⟨q, List.mem_append_right _ (by simp [hsel]), b, List.mem_append_left _ hb, hqb⟩

/-- Page 428: an available uncovered target forces strict decrease of the holes count. -/
theorem holes_lt_of_available (B : List ℕ) (N : ℕ) (hN : 8 ≤ N) (he : Even N)
    (hnot : covered B N = false) (ha : ∃ a, bestA 3 B N = some a) :
    (holes (B ++ [selected 3 B 8]) N).card < (holes B N).card := by
  obtain ⟨t, htlo, hthi, hteven, htfalse, httrue⟩ := selected_progress B N hN he hnot ha
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨holes_antitone B _ (fun _ hb => List.mem_append_left _ hb) N, ?_⟩
  intro heq
  have hmem : t ∈ holes B N := by
    simp only [holes, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, htlo, hteven, htfalse⟩
  have hmem' : t ∈ holes (B ++ [selected 3 B 8]) N := by rw [heq]; exact hmem
  have hfalse := (Finset.mem_filter.mp hmem').2.2.2
  rw [httrue] at hfalse
  contradiction

/-- Page 428, as a consequence: a permanently available target is eventually covered. -/
theorem eventually_covers_available (N n0 : ℕ) (hN : 8 ≤ N) (he : Even N)
    (hAvail : ∀ n, n0 ≤ n → ∃ a, bestA 3 (primePrefix n) N = some a) :
    ∃ n, n0 ≤ n ∧ covered (primePrefix n) N = true := by
  by_contra hnone
  have hfalse : ∀ k, covered (primePrefix (n0 + k)) N = false := by
    intro k
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact hnone ⟨n0 + k, by omega, htrue⟩
  apply not_strictAnti_of_wellFoundedLT (fun k => (holes (primePrefix (n0 + k)) N).card)
  apply strictAnti_nat_of_succ_lt
  intro k
  have hh := holes_lt_of_available (primePrefix (n0 + k)) N hN he (hfalse k)
    (hAvail (n0 + k) (by omega))
  simp only [primePrefix]
  omega

/-- Page 428, as a consequence: sums of retained basis elements with input primes
are eventually represented by two selected basis elements. -/
theorem eventually_covers_prime_complement (n0 b p : ℕ) (hb : b ∈ primePrefix n0) (hp : p.Prime) (h3 : 3 ≤ p) :
    ∃ n, n0 ≤ n ∧ covered (primePrefix n) (b + p) = true := by
  have hbprime := prefix_primes n0 b hb
  have hbo : Odd b := hbprime.1.odd_of_ne_two (by omega)
  have hpo : Odd p := hp.odd_of_ne_two (by omega)
  have he : Even (b + p) := hbo.add_odd hpo
  by_cases hN : 8 ≤ b + p
  · apply eventually_covers_available (b + p) n0 hN he
    intro n hn
    have hb' := prefix_subset n0 n hn hb
    rw [bestA_eq_max?]
    apply Option.isSome_iff_exists.mp
    apply List.isSome_max?_of_mem
    exact (mem_candidates_iff 3 (primePrefix n) (b + p) p).mpr
      ⟨hp, h3, b, hb', Nat.add_comm p b⟩
  · have heven := Nat.even_iff.mp he
    have hp3 : p = 3 := by omega
    subst p
    exact ⟨n0, le_rfl, (covered_iff _ _).mpr ⟨b, hb, 3, prefix_seed n0, rfl⟩⟩

end LeanLab.Stein1965.Coverage114

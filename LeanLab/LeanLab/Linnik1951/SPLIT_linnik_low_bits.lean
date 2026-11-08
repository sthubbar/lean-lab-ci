import LeanLab.Linnik1951.Novelty1620

/-!
# Split of `linnik_low_bits`, `Linnik1951/Novelty1620`

`linnik_low_bits` states: under GRH, for every real `θ` with `1 / 2 < θ < 1` there is `k₀` such
that every sufficiently large even `N` is a sum of two primes and exactly `k` powers of two, each
power at most `N ^ θ`, for every `k ≥ k₀`.

The split goes through a single power count `K`.

* `leaf_grh_powers_within_window`, the analytic input: one count `K` and one threshold such that
  every large even `N` is two primes plus at most `K` powers of two of size at most `N ^ θ`, and
  those powers sum to at least `2 * K`.
* `leaf_split_at_most_to_exact`, the binary splitting estimate: a sum of at most `K` powers of two
  that is at least `2 * K` is also a sum of exactly `K` powers of two, none of them larger.
* `leaf_rep_add_one_power`, one step up in the count at the cost of shifting `N` by two: a
  representation of `N - 2` with `k` powers gives one of `N` with `k + 1` powers.
* `leaf_rpow_ge_two`, the numeric side condition of that step: `2 ≤ N ^ θ` for `N ≥ 4`.

Assembly: the analytic leaf supplies `k = K` for all large even `N`, the splitting leaf turns
"at most" into "exactly", and the step leaf raises the count one at a time, so every `k ≥ K` is
covered. This file proves nothing about the four leaves, which stay open.
-/

namespace LeanLab.Linnik1951.Novelty1620

open LeanLab.Linnik LeanLab.DERZ1997

/-! ### Private helpers for the leaves

A power `2 ^ e` splits into two copies of `2 ^ (e - 1)`; a sum of powers of two can therefore be
refined one term at a time while keeping its value, up to `M / 2` terms; and a list of exponents of
length `K` gives the `Fin K`-indexed family that `LowBitsRep` asks for. Nothing here changes a
statement or a definition of the lab. -/

/-- `2 ^ e` is two copies of `2 ^ (e - 1)` when `1 ≤ e`. -/
private lemma two_pow_split {e : ℕ} (he : 1 ≤ e) : 2 ^ e = 2 ^ (e - 1) + 2 ^ (e - 1) := by
  have h : e = (e - 1) + 1 := by omega
  conv_lhs => rw [h]
  rw [pow_succ]
  ring

/-- The real power `2 ^ (e - 1)` does not exceed `2 ^ e`. -/
private lemma two_rpow_pred_le {e : ℕ} (he : 1 ≤ e) : (2 : ℝ) ^ (e - 1) ≤ (2 : ℝ) ^ e :=
  pow_le_pow_right₀ (by norm_num) (by omega)

/-- `2 ≤ N ^ θ` for `N ≥ 4` and `θ ≥ 1 / 2`, the numeric side condition of step 3:
`2 = 4 ^ (1 / 2) ≤ 4 ^ θ ≤ N ^ θ`. -/
private lemma two_le_rpow {θ : ℝ} (hθ : 1 / 2 ≤ θ) {N : ℕ} (hN : 4 ≤ N) :
    (2 : ℝ) ≤ (N : ℝ) ^ θ := by
  have hsqrt : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
    rw [← Real.sqrt_eq_rpow]
    norm_num
  have hstep1 : (4 : ℝ) ^ ((1 : ℝ) / 2) ≤ (4 : ℝ) ^ θ :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ
  have hcast : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hstep2 : (4 : ℝ) ^ θ ≤ (N : ℝ) ^ θ :=
    Real.rpow_le_rpow (by norm_num) hcast (by linarith)
  linarith

/-- A list all of whose entries are `1` has power-sum `2 * length`. -/
private lemma sum_pow_of_all_one (l : List ℕ) :
    (∀ e ∈ l, e = 1) → (l.map (fun e => 2 ^ e)).sum = 2 * l.length := by
  induction l with
  | nil => intro _; simp
  | cons a rest ih =>
    intro h
    have ha : a = 1 := h a (by simp)
    have hrest : ∀ e ∈ rest, e = 1 := fun e he => h e (by simp [he])
    rw [List.map_cons, List.sum_cons, List.length_cons, ih hrest, ha, pow_one]
    ring

/-- One split step. A list of exponents with `1 ≤ e`, `2 ^ e ≤ X` and some entry `2 ≤ e` is
replaced by a longer list with the same power-sum, all conditions preserved: the entry `e ≥ 2`
becomes two copies of `e - 1`. -/
private lemma split_list_step {X : ℝ} (l : List ℕ) :
    (∀ e ∈ l, 1 ≤ e) → (∀ e ∈ l, (2 : ℝ) ^ e ≤ X) → (∃ e ∈ l, 2 ≤ e) →
      ∃ l' : List ℕ, l'.length = l.length + 1 ∧
        (l'.map (fun e => 2 ^ e)).sum = (l.map (fun e => 2 ^ e)).sum ∧
          (∀ e ∈ l', 1 ≤ e) ∧ (∀ e ∈ l', (2 : ℝ) ^ e ≤ X) := by
  induction l with
  | nil => rintro _ _ ⟨e, he, -⟩; simp at he
  | cons a rest ih =>
    intro h1 h2 hex
    by_cases ha : 2 ≤ a
    · refine ⟨(a - 1) :: (a - 1) :: rest, by simp, ?_, ?_, ?_⟩
      · have hp : 2 ^ a = 2 ^ (a - 1) + 2 ^ (a - 1) := two_pow_split (by omega)
        simp only [List.map_cons, List.sum_cons]
        rw [hp]
        ring
      · intro z hz
        rcases List.mem_cons.1 hz with hz1 | hz
        · rw [hz1]; omega
        · rcases List.mem_cons.1 hz with hz2 | hz
          · rw [hz2]; omega
          · exact h1 z (List.mem_cons_of_mem a hz)
      · intro z hz
        rcases List.mem_cons.1 hz with hz1 | hz
        · rw [hz1]; exact le_trans (two_rpow_pred_le (by omega)) (h2 a (by simp))
        · rcases List.mem_cons.1 hz with hz2 | hz
          · rw [hz2]; exact le_trans (two_rpow_pred_le (by omega)) (h2 a (by simp))
          · exact h2 z (List.mem_cons_of_mem a hz)
    · obtain ⟨e, he, he2⟩ := hex
      have he_rest : e ∈ rest := by
        rcases List.mem_cons.1 he with heq | h
        · rw [heq] at he2
          omega
        exact h
      obtain ⟨l', hl', hsum', h1', h2'⟩ :=
        ih (fun z hz => h1 z (List.mem_cons_of_mem a hz))
          (fun z hz => h2 z (List.mem_cons_of_mem a hz)) ⟨e, he_rest, he2⟩
      refine ⟨a :: l', by simp [hl'], ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons]
        rw [hsum']
      · intro z hz
        rcases List.mem_cons.1 hz with hz1 | hz
        · rw [hz1]; exact h1 a (by simp)
        · exact h1' z hz
      · intro z hz
        rcases List.mem_cons.1 hz with hz1 | hz
        · rw [hz1]; exact h2 a (by simp)
        · exact h2' z hz

/-- Iterating `split_list_step`: from a list of length at most `K - n` one reaches a list `n` terms
longer with the same power-sum and the same pointwise bounds. The step is possible because a list
of `1`s has power-sum `2 * length`, so `2 * K ≤ power-sum` forces a `2` somewhere while the length
is below `K`. -/
private lemma split_list_iter {X : ℝ} {K : ℕ} (n : ℕ) :
    ∀ (l : List ℕ), (∀ e ∈ l, 1 ≤ e) → (∀ e ∈ l, (2 : ℝ) ^ e ≤ X) →
      2 * K ≤ (l.map (fun e => 2 ^ e)).sum → l.length + n ≤ K →
      ∃ l' : List ℕ, l'.length = l.length + n ∧
        (l'.map (fun e => 2 ^ e)).sum = (l.map (fun e => 2 ^ e)).sum ∧
          (∀ e ∈ l', 1 ≤ e) ∧ (∀ e ∈ l', (2 : ℝ) ^ e ≤ X) := by
  induction n with
  | zero => intro l h1 h2 _ _; exact ⟨l, by simp, rfl, h1, h2⟩
  | succ n ih =>
    intro l h1 h2 hS hlen
    have hex : ∃ e ∈ l, 2 ≤ e := by
      by_contra hc
      push_neg at hc
      have hall : ∀ e ∈ l, e = 1 := by
        intro e he
        have h1e := h1 e he
        have hce := hc e he
        omega
      have hs : (l.map (fun e => 2 ^ e)).sum = 2 * l.length := sum_pow_of_all_one l hall
      omega
    obtain ⟨l1, hl1, hsum1, h1', h2'⟩ := split_list_step l h1 h2 hex
    obtain ⟨l', hl', hsum', h1'', h2''⟩ :=
      ih l1 h1' h2' (by rw [hsum1]; exact hS) (by omega)
    exact ⟨l', by omega, by rw [hsum', hsum1], h1'', h2''⟩

/-- A list of exponents of length `n` whose powers are all `≥ 1` and at most `X` gives the
`Fin n`-indexed family of `LowBitsRep`, with the same power-sum. -/
private lemma exists_rep_of_list {X : ℝ} {n M : ℕ} (l : List ℕ) (hlen : l.length = n)
    (h1 : ∀ e ∈ l, 1 ≤ e) (h2 : ∀ e ∈ l, (2 : ℝ) ^ e ≤ X)
    (hsum : M = (l.map (fun e => 2 ^ e)).sum) :
    ∃ ν' : Fin n → ℕ, (∀ i, 1 ≤ ν' i ∧ (2 : ℝ) ^ (ν' i) ≤ X) ∧ M = ∑ i, 2 ^ (ν' i) := by
  subst hlen
  refine ⟨l.get, fun i => ⟨h1 _ (List.get_mem l i), h2 _ (List.get_mem l i)⟩, ?_⟩
  rw [hsum, ← List.sum_ofFn]
  congr 2
  apply List.ext_get <;> simp

/-- LEAF. Step 1 of the split, the analytic input. Assume GRH. For every real `θ` with
`1 / 2 < θ < 1` there are `K` and `N₀` such that every even `N > N₀` is a sum of two primes and
at most `K` powers of two `2 ^ ν i` with `1 ≤ ν i` and `2 ^ ν i ≤ N ^ θ`, and the powers sum to at
least `2 * K`. The count `K` is one fixed number, not yet the exact count `k` of the target. -/
theorem leaf_grh_powers_within_window (hG : GRH) :
    ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
      ∃ K N₀ : ℕ, ∀ N : ℕ, Even N → N₀ < N →
        ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
          ∃ t : ℕ, t ≤ K ∧ ∃ ν : Fin t → ℕ,
            (∀ i, 1 ≤ ν i ∧ (2 : ℝ) ^ (ν i) ≤ (N : ℝ) ^ θ) ∧
              N = p + q + ∑ i, 2 ^ (ν i) ∧ 2 * K ≤ ∑ i, 2 ^ (ν i) := by
  sorry

/-- LEAF. Step 2 of the split, the binary splitting estimate. Let `0 ≤ X`, let `M` be a sum of
`t ≤ K` powers of two `2 ^ ν i` with `1 ≤ ν i` and `2 ^ ν i ≤ X`, and let `2 * K ≤ M`. Then `M` is
also a sum of exactly `K` powers of two with `1 ≤ ν' i` and `2 ^ ν' i ≤ X`. Splitting `2 ^ e` with
`2 ≤ e` into `2 ^ (e - 1) + 2 ^ (e - 1)` raises the count by one and lowers no single power, so
every count from `t` up to `M / 2` is reached, and `2 * K ≤ M` puts `K` in that range. -/
theorem leaf_split_at_most_to_exact {K M : ℕ} {X : ℝ} (hX : 0 ≤ X)
    (hK : 2 * K ≤ M) (t : ℕ) (ht : t ≤ K) (ν : Fin t → ℕ)
    (hν : ∀ i, 1 ≤ ν i ∧ (2 : ℝ) ^ (ν i) ≤ X)
    (hM : M = ∑ i, 2 ^ (ν i)) :
    ∃ ν' : Fin K → ℕ, (∀ i, 1 ≤ ν' i ∧ (2 : ℝ) ^ (ν' i) ≤ X) ∧ M = ∑ i, 2 ^ (ν' i) := by
  have hl : (List.ofFn ν).length = t := List.length_ofFn
  have hsum0 : ((List.ofFn ν).map (fun e => 2 ^ e)).sum = ∑ i, 2 ^ (ν i) := by
    rw [List.map_ofFn, Fin.sum_ofFn]
    simp
  have h1 : ∀ e ∈ List.ofFn ν, 1 ≤ e :=
    List.forall_mem_ofFn_iff.mpr (fun j => (hν j).1)
  have h2 : ∀ e ∈ List.ofFn ν, (2 : ℝ) ^ e ≤ X :=
    List.forall_mem_ofFn_iff.mpr (fun j => (hν j).2)
  have hS : 2 * K ≤ ((List.ofFn ν).map (fun e => 2 ^ e)).sum := by
    rw [hsum0, ← hM]
    exact hK
  obtain ⟨l', hl', hsum', h1', h2'⟩ :=
    split_list_iter (K := K) (K - t) (List.ofFn ν) h1 h2 hS (by rw [hl]; omega)
  exact exists_rep_of_list l' (by omega) h1' h2' (by rw [hM, ← hsum0, ← hsum'])

/-- LEAF. Step 3 of the split, one step in the count. For `1 / 2 ≤ θ` and `4 ≤ N`, a
representation of `N - 2` as two primes plus `k` powers of two, each at most `(N - 2) ^ θ`, gives a
representation of `N` as two primes plus `k + 1` powers of two each at most `N ^ θ`: append the
power `2 ^ 1 = 2`, and `(N - 2) ^ θ ≤ N ^ θ` because `θ ≥ 0`. -/
theorem leaf_rep_add_one_power {θ : ℝ} (hθ : 1 / 2 ≤ θ) {k N : ℕ} (hN : 4 ≤ N)
    (h : LowBitsRep θ k (N - 2)) : LowBitsRep θ (k + 1) N := by
  obtain ⟨p, q, hp, hq, ν, hν, hsum⟩ := h
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hcast : ((N - 2 : ℕ) : ℝ) ≤ (N : ℝ) := by
    have hle : N - 2 ≤ N := Nat.sub_le N 2
    exact_mod_cast hle
  have hmono : ((N - 2 : ℕ) : ℝ) ^ θ ≤ (N : ℝ) ^ θ :=
    Real.rpow_le_rpow (by positivity) hcast hθ0
  have h2N : (2 : ℝ) ≤ (N : ℝ) ^ θ := two_le_rpow hθ hN
  have h1 : ∀ e ∈ List.ofFn ν ++ [1], 1 ≤ e := by
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact List.forall_mem_ofFn_iff.mpr (fun j => (hν j).1) e he
    · rw [List.mem_singleton.1 he]
  have h2 : ∀ e ∈ List.ofFn ν ++ [1], (2 : ℝ) ^ e ≤ (N : ℝ) ^ θ := by
    intro e he
    rcases List.mem_append.1 he with he | he
    · have hb : ∀ a ∈ List.ofFn ν, (2 : ℝ) ^ a ≤ ((N - 2 : ℕ) : ℝ) ^ θ :=
        List.forall_mem_ofFn_iff.mpr (fun j => (hν j).2)
      exact le_trans (hb e he) hmono
    · rw [List.mem_singleton.1 he, pow_one]
      exact h2N
  have hlen : (List.ofFn ν ++ [1]).length = k + 1 := by simp
  have hlsum : ((List.ofFn ν ++ [1]).map (fun e => 2 ^ e)).sum = (∑ i, 2 ^ ν i) + 2 := by
    rw [List.map_append, List.sum_append, List.map_ofFn, Fin.sum_ofFn]
    simp
  obtain ⟨ν', hν', hsum'⟩ :=
    exists_rep_of_list (M := (∑ i, 2 ^ ν i) + 2) (List.ofFn ν ++ [1]) hlen h1 h2 hlsum.symm
  exact ⟨p, q, hp, hq, ν', hν', by rw [← hsum']; omega⟩

/-- LEAF. Step 4 of the split, the numeric side condition of step 3 and nothing more:
`2 ≤ N ^ θ` for every `N ≥ 4` and every `θ ≥ 1 / 2`, since `2 = 4 ^ (1 / 2) ≤ 4 ^ θ ≤ N ^ θ`. -/
theorem leaf_rpow_ge_two {θ : ℝ} (hθ : 1 / 2 ≤ θ) {N : ℕ} (hN : 4 ≤ N) :
    (2 : ℝ) ≤ (N : ℝ) ^ θ := by
  exact two_le_rpow hθ hN

/-- `linnik_low_bits` of `Novelty1620`, assembled from the four leaves above: the analytic leaf
gives the count `K` for all large even `N`, the splitting leaf makes the count exact, and the
count-raising leaf covers every `k ≥ K`. -/
theorem linnik_low_bits_split (_hG : GRH) :
    ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → AllLargeEven (LowBitsRep θ k) := by
  intro θ hθ1 hθ2
  obtain ⟨K, N₀, hN₀⟩ := leaf_grh_powers_within_window _hG θ hθ1 hθ2
  have hθhalf : 1 / 2 ≤ θ := le_of_lt hθ1
  have base : AllLargeEven (LowBitsRep θ K) := by
    refine ⟨N₀, ?_⟩
    intro N hEven hN
    obtain ⟨p, q, hp, hq, t, ht, ν, hν, hNsum, hKle⟩ := hN₀ N hEven hN
    obtain ⟨ν', hν', hsum⟩ :=
      leaf_split_at_most_to_exact (K := K) (M := ∑ i, 2 ^ (ν i)) (X := (N : ℝ) ^ θ)
        (Real.rpow_nonneg (Nat.cast_nonneg N) θ) hKle t ht ν hν rfl
    exact ⟨p, q, hp, hq, ν', hν', by rw [hNsum, hsum]⟩
  have step : ∀ k : ℕ, K ≤ k → AllLargeEven (LowBitsRep θ k) →
      AllLargeEven (LowBitsRep θ (k + 1)) := by
    intro k _ hAle
    obtain ⟨M₀, hM₀⟩ := hAle
    refine ⟨M₀ + 6, ?_⟩
    intro N hEven hN
    obtain ⟨m, hm⟩ := hEven
    have hN8 : 8 ≤ N := by omega
    have hEven' : Even (N - 2) := ⟨m - 1, by omega⟩
    have hlt : M₀ < N - 2 := by omega
    exact leaf_rep_add_one_power hθhalf (by omega : 4 ≤ N) (hM₀ (N - 2) hEven' hlt)
  refine ⟨K, ?_⟩
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact base
  | succ n hn ih => exact step n hn ih

end LeanLab.Linnik1951.Novelty1620

#print axioms LeanLab.Linnik1951.Novelty1620.linnik_low_bits_split

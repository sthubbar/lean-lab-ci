import Mathlib

lemma residue_congruence (m q : ℕ)
    (hm : m = 9 ∨ m = 25 ∨ m = 49 ∨ m = 121) :
    2 * (((q % m + m - 10 ^ 250 % m) % m) * ((m + 1) / 2)) + 10 ^ 250 ≡ q [MOD m] := by
  rcases hm with rfl | rfl | rfl | rfl <;>
    norm_num [Nat.ModEq, Nat.add_mod, Nat.mul_mod] <;> omega

lemma modulus_not_prime (m : ℕ)
    (hm : m = 9 ∨ m = 25 ∨ m = 49 ∨ m = 121) : ¬ m.Prime := by
  rcases hm with rfl | rfl | rfl | rfl <;> decide

theorem no_at_most_four_prime_cover (a b : ℕ)
    (hblock : b - a > 1334025) (ha : 1334025 ≤ a) :
    ¬ (∃ qs : List ℕ, qs.length ≤ 4 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, a ≤ j → j < b →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true)) := by
  rintro ⟨qs, hlen, hpr, hcov⟩
  let mod : Fin 4 → ℕ := fun i => [9, 25, 49, 121].getD i.val 0
  let pad : List ℕ := qs ++ [0, 0, 0, 0]
  let qAt : Fin 4 → ℕ := fun i => pad.getD i.val 0
  let res : Fin 4 → ℕ := fun i =>
    ((qAt i % mod i + mod i - 10 ^ 250 % mod i) % mod i) * ((mod i + 1) / 2)
  trace_state
  have hpair : List.Pairwise (fun x y => mod x).Coprime (List.finRange 4) := by
    decide
  trace_state
  have hnz : ∀ i ∈ List.finRange 4, mod i ≠ 0 := by
    intro i hi
    fin_cases i <;> simp [mod]
  let crt := Nat.chineseRemainderOfList res mod (List.finRange 4) hpair
  trace_state
  trace_state
  have hj0 : (crt : ℕ) < 1334025 := by
    have h := Nat.chineseRemainderOfList_lt_prod res mod (List.finRange 4) hpair hnz
    norm_num [List.finRange, List.map, mod] at h
    exact h
  trace_state
  let j : ℕ := (crt : ℕ) + 1334025 *
    ((a - (crt : ℕ) + 1334025 - 1) / 1334025)
  have hjlo : a ≤ j := by
    dsimp [j]
    omega
  have hjhi : j < a + 1334025 := by
    dsimp [j]
    omega
  have hjlt : j < b := by
    omega
  trace_state
  have hjres (i : Fin 4) : j ≡ res i [MOD mod i] := by
    have hc := crt.prop i (by simp)
    fin_cases i <;>
      simp [j, res, mod, Nat.ModEq, Nat.add_mod, Nat.mul_mod] at * <;>
      omega
  trace_state
  trace_state
  have hcover := hcov j hjlo hjlt
  rw [List.any_eq_true] at hcover
  rcases hcover with ⟨q, hqmem, hqbool⟩
  have hqcond : q ≤ 10 ^ 250 + 2 * j ∧
      (10 ^ 250 + 2 * j - q).Prime := by
    simpa using hqbool
  rcases List.mem_iff_get.mp hqmem with ⟨n, hn⟩
  let i : Fin 4 := ⟨n.val, by omega⟩
  have hqAt : qAt i = q := by
    dsimp [qAt, pad]
    rw [List.getD_append _ _ 0 n.val n.isLt]
    simp [List.getD_eq_getElem qs 0 n.isLt, n, hn]
  have hmcase : mod i = 9 ∨ mod i = 25 ∨ mod i = 49 ∨ mod i = 121 := by
    fin_cases i <;> simp [mod]
  have hra : 2 * res i + 10 ^ 250 ≡ q [MOD mod i] := by
    apply residue_congruence (mod i) (qAt i) hmcase
    simp [res, hqAt]
  have htwo : 2 * j ≡ 2 * res i [MOD mod i] := by
    have h := (hjres i).mul (Nat.ModEq.refl 2)
    simpa [Nat.mul_comm] using h
  have htotal : 10 ^ 250 + 2 * j ≡ q [MOD mod i] := by
    have h := htwo.add (Nat.ModEq.refl (10 ^ 250))
    have h' := h.trans hra
    simpa [Nat.add_comm, Nat.mul_comm] using h'
  have hdiv : mod i ∣ 10 ^ 250 + 2 * j - q :=
    (htotal.symm).dvd' hqcond.1
  have hnot : ¬ (10 ^ 250 + 2 * j - q).Prime := by
    intro hd
    rcases Nat.dvd_prime hd hdiv with hm1 | hmd
    · omega
    · exact modulus_not_prime (mod i) hmcase (by simpa [hmd] using hd)
  exact hnot hqcond.2

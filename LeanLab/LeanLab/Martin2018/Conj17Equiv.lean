/-
Martin 2018, P0084, the remark after Conjecture 1.7: "our calculations suggest E_{5,5,6} = {4},
which would imply E_{2,2,3} = ∅, so in the conjecture we can take p + q to be an arbitrary even
number which is 1 mod 3, and then r ∈ {3, 5, 7}."
PROVED zero sorry: E_{5,5,6} ⊆ {4} implies E_{2,2,3} = ∅, and Conj 1.7 ↔ E_{2,2,3} = ∅.
The direction E_{2,2,3} = ∅ → Conj 1.7 is the paper's remark. The converse, Conj 1.7 → E_{2,2,3} = ∅,
is not stated in the paper: for even n ≡ 1 mod 3 apply Conj 1.7 to n + 3; then r ≡ 0 mod 3, so
r = 3. It is elementary; we claim no novelty.
AI-written Lean code, Claude, run 20261016T2204Z-20593. Checked only by the Lean kernel.
Conjecture 1.7 is OPEN.
-/
import Mathlib
import LeanLab.Martin2018.Conj15

namespace LeanLab.Martin2018

/-- If a prime is divisible by 3 it is 3. -/
theorem prime_mod3_zero {r : ℕ} (hr : r.Prime) (h : r % 3 = 0) : r = 3 := by
  have h3 : 3 ∣ r := Nat.dvd_of_mod_eq_zero h
  rcases hr.eq_one_or_self_of_dvd 3 h3 with h1 | h1 <;> omega

theorem conj1_7_imp_E223 (h : Conj1_7) : Eset 3 2 2 = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro n ⟨hpos, ⟨k, hk⟩, hmod, hno⟩
  have hn4 : 4 ≤ n := by omega
  obtain ⟨p, q, r, hp, hq, hr, hp3, hq3, hsum⟩ := h (n + 3) ⟨k + 1, by omega⟩ (by omega)
  have hr3 : r = 3 := prime_mod3_zero hr (by omega)
  exact hno ⟨p, q, hp, hq, by omega, by omega, by omega⟩

theorem conj1_7_of_E223 (h : Eset 3 2 2 = ∅) : Conj1_7 := by
  intro n ⟨k, hk⟩ h5
  have key : ∀ m, 0 < m → Even m → m % 3 = 1 → GoldbachAP 3 2 2 m := by
    intro m hm he hmod
    by_contra hc
    have : m ∈ Eset 3 2 2 := ⟨hm, he, by omega, hc⟩
    rw [h] at this; exact this
  have hrep : ∀ r, r.Prime → r % 2 = 1 → n % 3 = (1 + r) % 3 → r + 4 ≤ n →
      ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p % 3 = 2 ∧ q % 3 = 2 ∧ p + q + r = n := by
    intro r hr hodd hmod hle
    obtain ⟨p, q, hp, hq, hp3, hq3, hpq⟩ :=
      key (n - r) (by omega) ⟨(n - r) / 2, by omega⟩ (by omega)
    exact ⟨p, q, r, hp, hq, hr, by omega, by omega, by omega⟩
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h0 | h1 | h2
  · exact hrep 5 (by norm_num) rfl (by omega) (by omega)
  · exact hrep 3 Nat.prime_three rfl (by omega) (by omega)
  · exact hrep 7 (by norm_num) rfl (by omega) (by omega)

/-- Conjecture 1.7 is equivalent to `E_{2,2,3} = ∅`. -/
theorem conj1_7_iff_E223 : Conj1_7 ↔ Eset 3 2 2 = ∅ :=
  ⟨conj1_7_imp_E223, conj1_7_of_E223⟩

/-- The paper's step: `E_{5,5,6} ⊆ {4}` gives `E_{2,2,3} = ∅`. -/
theorem E223_of_E556 (h : Eset 6 5 5 ⊆ {4}) : Eset 3 2 2 = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro n ⟨hpos, ⟨k, hk⟩, hmod, hno⟩
  by_cases h4 : n = 4
  · subst h4
    exact hno ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl, rfl, rfl⟩
  · have hnot : n ∉ Eset 6 5 5 := fun hm => h4 (h hm)
    have hG : GoldbachAP 6 5 5 n := by
      by_contra hc
      exact hnot ⟨hpos, ⟨k, hk⟩, by omega, hc⟩
    obtain ⟨p, q, hp, hq, hp6, hq6, hpq⟩ := hG
    exact hno ⟨p, q, hp, hq, by omega, by omega, hpq⟩

/-- So the paper's computed `E_{5,5,6} = {4}` would give Conjecture 1.7. -/
theorem conj1_7_of_E556 (h : Eset 6 5 5 ⊆ {4}) : Conj1_7 :=
  conj1_7_of_E223 (E223_of_E556 h)

end LeanLab.Martin2018

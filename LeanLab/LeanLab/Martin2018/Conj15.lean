/-
Martin 2018, P0084, arXiv 1806.00946v1: the exceptional sets E_{a,b,m}, Conjecture 1.5 on
their growth, Conjecture 1.6, and the paper's remark that binary Goldbach is equivalent to
E_{1,1,2} = {2, 4}.
Paper, section 1: "Denote by E_{a,b,m} the set of positive even n ≡ a + b mod m which are
not of the form asserted in the conjecture", that is n = p + q with p ≡ a, q ≡ b mod m.
STATED: Conj 1.5 i, ii and Conj 1.6, all OPEN. O as m → ∞ is read as: some C and M with the
bound for every m ≥ M. L_avg uses Set.ncard, so Conj 1.5 ii also asserts every admissible
E_{a,b,m} is finite, which the average needs to make sense.
PROVED zero sorry: binary Goldbach ↔ E_{1,1,2} = {2, 4}.
AI-written Lean code, Claude, run 20261016T2204Z-20593. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Martin2018.Statements

namespace LeanLab.Martin2018

open Real

/-- `E_{a,b,m}`: positive even `n ≡ a + b` mod `m` that are not `p + q` with `p ≡ a`,
`q ≡ b` mod `m`. -/
def Eset (m a b : ℕ) : Set ℕ :=
  {n | 0 < n ∧ Even n ∧ n % m = (a + b) % m ∧ ¬ GoldbachAP m a b n}

/-- `(a, b, m)` admissible: `a, b` are unit residues mod `m`, taken as representatives
below `m`. -/
def Admissible (m a b : ℕ) : Prop := a < m ∧ b < m ∧ Nat.Coprime a m ∧ Nat.Coprime b m

/-- The unit residues below `m`. -/
def units (m : ℕ) : Finset ℕ := (Finset.range m).filter (fun a => Nat.Coprime a m)

/-- Conj 1.5 i: `E_max(m) = O(m² (log m)²)`. -/
def Conj1_5_i : Prop :=
  ∃ C : ℝ, ∃ M : ℕ, ∀ m, M ≤ m → ∀ a b, Admissible m a b → ∀ n ∈ Eset m a b,
    (n : ℝ) ≤ C * (m : ℝ) ^ 2 * (Real.log m) ^ 2

/-- `L_avg(m) = φ(m)^{-2} Σ_{a,b} |E_{a,b,m}|`. -/
noncomputable def Lavg (m : ℕ) : ℝ :=
  (1 / (Nat.totient m : ℝ) ^ 2) *
    ∑ a ∈ units m, ∑ b ∈ units m, ((Eset m a b).ncard : ℝ)

/-- Conj 1.5 ii: every admissible `E_{a,b,m}` is finite and `L_avg(m) = O(m^ε)` for every
`ε > 0`. -/
def Conj1_5_ii : Prop :=
  (∀ m a b, Admissible m a b → (Eset m a b).Finite) ∧
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∃ M : ℕ, ∀ m, M ≤ m → Lavg m ≤ C * (m : ℝ) ^ ε

/-- Conj 1.6: infinitely many admissible `(a, b, m)` with `E_{a,b,m}` empty. -/
def Conj1_6 : Prop :=
  {t : ℕ × ℕ × ℕ | Admissible t.2.2 t.1 t.2.1 ∧ Eset t.2.2 t.1 t.2.1 = ∅}.Infinite

/-! ### The paper's remark: binary Goldbach is equivalent to `E_{1,1,2} = {2, 4}` -/

theorem two_mem_E112 : 2 ∈ Eset 2 1 1 := by
  refine ⟨by norm_num, even_two, by norm_num, ?_⟩
  rintro ⟨p, q, hp, hq, -, -, h⟩
  have := hp.two_le; have := hq.two_le; omega

theorem four_mem_E112 : 4 ∈ Eset 2 1 1 := by
  refine ⟨by norm_num, by decide, by norm_num, ?_⟩
  rintro ⟨p, q, hp, hq, hp2, -, h⟩
  have := hp.two_le; have := hq.two_le
  have : p = 2 := by omega
  subst this; simp at hp2

theorem goldbach_iff_E112 : BinaryGoldbach ↔ Eset 2 1 1 = {2, 4} := by
  constructor
  · intro hG
    ext n
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hn0, hne, -, hno⟩
      by_contra hc
      push_neg at hc
      have h6 : 6 ≤ n := by
        obtain ⟨k, rfl⟩ := hne; omega
      obtain ⟨p, q, hp, hq, hpq⟩ := hG n hne (by omega)
      apply hno
      have hp2 : p ≠ 2 := by
        rintro rfl
        have hqe : Even q := by
          have : q = n - 2 := by omega
          rw [this]; obtain ⟨k, hk⟩ := hne; exact ⟨k - 1, by omega⟩
        have := (hq.even_iff).mp hqe; omega
      have hq2 : q ≠ 2 := by
        rintro rfl
        have hpe : Even p := by
          have : p = n - 2 := by omega
          rw [this]; obtain ⟨k, hk⟩ := hne; exact ⟨k - 1, by omega⟩
        have := (hp.even_iff).mp hpe; omega
      exact ⟨p, q, hp, hq, by have := Nat.odd_iff.mp (hp.odd_of_ne_two hp2); omega,
        by have := Nat.odd_iff.mp (hq.odd_of_ne_two hq2); omega, hpq⟩
    · rintro (rfl | rfl)
      · exact two_mem_E112
      · exact four_mem_E112
  · intro hE n hne h4
    rcases Nat.eq_or_lt_of_le h4 with h | h
    · subst h; exact ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl⟩
    · have hn : n ∉ Eset 2 1 1 := by
        rw [hE]; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega
      have hmod : n % 2 = (1 + 1) % 2 := by obtain ⟨k, rfl⟩ := hne; omega
      have : GoldbachAP 2 1 1 n := by
        by_contra hc; exact hn ⟨by omega, hne, hmod, hc⟩
      obtain ⟨p, q, hp, hq, -, -, hpq⟩ := this
      exact ⟨p, q, hp, hq, hpq⟩

end LeanLab.Martin2018

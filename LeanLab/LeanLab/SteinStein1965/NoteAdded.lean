/-
Stein and Stein 1965, P0073, unit U-0954, run 20261018T1603Z-12862.
Note added in proof, pp. 433-434: the two printed maximal decompositions, checked exactly.
Only the two printed rows are checked; the range claims up to `10^8` are cited.
Method: certificates of compositeness found by Python, a checker proved sound, run by
`decide +kernel`; primality of the large summands by the lab's trial division `primeB`.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
-/
import LeanLab.SteinStein1965.Soundness

namespace LeanLab.SteinStein1965

/-- `w` is a proper divisor of `n`. -/
def witOK (n w : ℕ) : Bool := decide (1 < w) && decide (w < n) && n % w == 0

theorem witOK_sound {n w : ℕ} (h : witOK n w = true) : 1 < n ∧ ¬ n.Prime := by
  simp only [witOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨by omega, fun hp => ?_⟩
  rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero h3) with h | h <;> omega

/-- For `q = p, p + s, p + 2 s, ...`, one witness each, showing `q` or `N - q` composite. -/
def certOK (N s : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | p, w :: ws => (witOK p w || witOK (N - p) w) && certOK N s (p + s) ws

theorem certOK_sound (N s : ℕ) : ∀ (ws : List ℕ) (p : ℕ), certOK N s p ws = true →
    ∀ k < ws.length, (1 < p + s * k ∧ ¬ (p + s * k).Prime) ∨
      (1 < N - (p + s * k) ∧ ¬ (N - (p + s * k)).Prime) := by
  intro ws
  induction ws with
  | nil => intro p _ k hk; simp at hk
  | cons w ws ih =>
    intro p h k hk
    simp only [certOK, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases k with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero]
      rcases h1 with h | h
      · exact Or.inl (witOK_sound h)
      · exact Or.inr (witOK_sound h)
    | succ k =>
      have := ih (p + s) h2 k (by simpa using hk)
      have e : p + s + s * k = p + s * (k + 1) := by ring
      rw [e] at this
      exact this

/-! ### `P(60119912) = 1093`, p. 433 -/

def certP : List ℕ := [
    47, 3, 5, 3, 3, 7, 3, 3, 383, 3, 3, 5, 3, 3, 31, 3, 5, 5, 3, 3, 79, 3, 3, 7, 3, 3, 5, 3, 3, 11,
    3, 5, 5, 3, 3, 13, 3, 7, 167, 3, 3, 5, 3, 3, 7, 3, 5, 5, 3, 3, 2719, 3, 3, 17, 3, 3, 5, 3, 7,
    11, 3, 5, 5, 3, 3, 7, 3, 3, 7, 3, 11, 5, 3, 3, 13, 3, 5, 5, 3, 7, 173, 3, 3, 13, 3, 3, 5, 3, 3,
    7, 3, 5, 11, 3, 3, 11, 3, 3, 109, 3, 7, 5, 3, 11, 17, 3, 5, 7, 3, 13, 7, 3, 3, 13, 3, 3, 5, 3,
    3, 283, 3, 5, 13, 3, 3, 11, 3, 3, 7, 3, 3, 5, 3, 3, 127, 3, 5, 5, 3, 3, 19, 3, 7, 17, 3, 3, 5,
    3, 13, 7, 3, 5, 5, 3, 3, 17, 3, 3, 11, 3, 17, 5, 3, 7, 29, 3, 5, 5, 3, 11, 7, 3, 3, 7, 3, 3, 5,
    3, 3, 19, 3, 5, 5, 3, 7, 23, 3, 13, 47, 3, 3, 5, 3, 3, 17, 3, 5, 5, 3, 3, 13, 3, 11, 113, 3, 7,
    5, 3, 3, 1069, 3, 5, 7, 3, 3, 7, 3, 19, 83, 3, 3, 5, 3, 3, 11, 3, 5, 5, 3, 3, 13, 3, 3, 7, 3,
    11, 5, 3, 3, 13, 3, 5, 5, 3, 3, 17, 3, 7, 37, 3, 3, 5, 3, 3, 7, 3, 5, 11, 3, 3, 11, 3, 17, 23,
    3, 13, 5, 3, 7, 13, 3, 5, 5, 3, 19, 7, 3, 3, 13, 3, 3, 5, 3, 3, 101, 3, 5, 5, 3, 7, 11, 3, 3,
    19, 3, 3, 5, 3, 3, 7, 3, 5, 5, 3, 13, 137, 3, 3, 13, 3, 7, 5, 3, 17, 2969, 3, 5, 7, 3, 3, 7, 3,
    3, 11, 3, 3, 5, 3, 3, 47, 3, 5, 23, 3, 11, 223, 3, 3, 7, 3, 3, 5, 3, 13, 61, 3, 5, 17, 3, 3,
    19, 3, 7, 43, 3, 23, 5, 3, 3, 7, 3, 5, 5, 3, 17, 71, 3, 11, 19, 3, 3, 5, 3, 7, 41, 3, 5, 5, 3,
    3, 7, 3, 13, 7, 3, 3, 5, 3, 19, 11, 3, 5, 5, 3, 7, 13, 3, 3, 17, 3, 11, 5, 3, 3, 7, 3, 5, 19,
    3, 3, 17, 3, 3, 4027, 3, 7, 5, 3, 3, 29, 3, 5, 7, 3, 23, 7, 3, 3, 59, 3, 3, 5, 3, 11, 13, 3, 5,
    5, 3, 3, 139, 3, 3, 7, 3, 19, 5, 3, 29, 17, 3, 5, 5, 3, 3, 11, 3, 7, 11, 3, 13, 5, 3, 3, 7, 3,
    5, 5, 3, 3, 23, 3, 3, 13, 3, 3, 5, 3, 7, 31, 3, 5, 5, 3, 3, 7, 3, 3, 11, 3, 3, 5, 3, 23, 79, 3,
    5, 5, 3, 7, 17, 3, 19, 13, 3, 3, 5, 3, 3, 7, 3, 5, 13, 3, 3, 127, 3, 17, 4507, 3, 7, 5, 3, 3,
    11, 3, 5, 7, 3, 3, 7, 3, 11, 2531, 3, 29, 5, 3, 13, 23, 3, 5, 5, 3, 3]

theorem certP_ok : certOK 60119912 2 3 certP = true ∧ certP.length = 545 := by
  decide +kernel

theorem prime_60118819 : Nat.Prime 60118819 := primeB_sound (by decide +kernel)

/-- p. 433: "the maximum value of `P(2n)` turns out to be 1093:
`60119912 = 1093 + 60118819`". Here: `P(60119912) = 1093` exactly. -/
theorem noteP_row : IsLeastGoldbachPrime 60119912 1093 := by
  refine ⟨by norm_num, by norm_num, prime_60118819, ?_⟩
  intro r h3 hr hp
  rcases Nat.even_or_odd r with he | ho
  · exact absurd (hp.even_iff.mp he) (by omega)
  · obtain ⟨j, rfl⟩ := ho
    have hk : j - 1 < certP.length := by rw [certP_ok.2]; omega
    have := certOK_sound 60119912 2 certP 3 certP_ok.1 (j - 1) hk
    have e : 3 + 2 * (j - 1) = 2 * j + 1 := by omega
    rw [e] at this
    rcases this with h | h
    · exact absurd hp h.2
    · exact h.2

/-! ### The `4m + 2` version, `P(76550462) = 2953`, p. 434 -/

def certP1 : List ℕ := [
    13, 3, 3, 19, 3, 3, 5, 3, 3, 5, 3, 3, 7, 3, 3, 29, 5, 3, 149, 7, 3, 5, 3, 3, 5, 3, 3, 11, 3, 3,
    11, 5, 3, 7, 3, 3, 5, 3, 3, 5, 7, 3, 13, 3, 3, 6907, 5, 3, 17, 3, 3, 5, 11, 3, 7, 13, 3, 23, 3,
    3, 11, 5, 3, 11, 3, 3, 5, 3, 3, 5, 3, 3, 17, 3, 3, 7, 5, 3, 13, 3, 3, 5, 7, 3, 5, 11, 3, 67, 3,
    3, 19, 5, 3, 7, 13, 3, 5, 3, 3, 5, 3, 3, 29, 7, 3, 379, 5, 3, 1741, 19, 3, 5, 3, 3, 5, 3, 3, 7,
    11, 3, 13, 5, 3, 17, 7, 3, 5, 3, 3, 11, 3, 3, 23, 13, 3, 7, 5, 3, 7, 3, 3, 5, 3, 3, 5, 7, 3,
    19, 3, 3, 17, 5, 3, 4583, 3, 3, 5, 17, 3, 7, 3, 3, 11, 3, 3, 1087, 5, 3, 2267, 3, 3, 5, 13, 3,
    17, 3, 3, 7, 23, 3, 7, 5, 3, 251, 11, 3, 5, 7, 3, 5, 3, 3, 11, 3, 3, 11, 5, 3, 13, 3, 3, 5, 3,
    3, 19, 3, 3, 31, 7, 3, 29, 5, 3, 59, 3, 3, 5, 11, 3, 5, 3, 3, 7, 19, 3, 17, 5, 3, 11, 7, 3, 5,
    3, 3, 5, 3, 3, 13, 3, 3, 31, 5, 3, 7, 3, 3, 5, 23, 3, 5, 7, 3, 17, 3, 3, 1171, 5, 3, 11, 17, 3,
    5, 3, 3, 7, 3, 3, 97, 29, 3, 23, 5, 3, 13, 3, 3, 5, 3, 3, 5, 19, 3, 7, 11, 3, 7, 5, 3, 19, 13,
    3, 5, 7, 3, 11, 3, 3, 29, 3, 3, 31, 5, 3, 7, 3, 3, 5, 3, 3, 5, 17, 3, 13, 7, 3, 13, 5, 3, 19,
    3, 3, 5, 3, 3, 5, 3, 3, 7, 13, 3, 4643, 5, 3, 31, 7, 3, 5, 19, 3, 23, 3, 3, 37, 3, 3, 7, 5, 3,
    7, 11, 3, 5, 3, 3, 13, 7, 3, 11, 3, 3, 11, 5, 3, 29, 31, 3, 5, 13, 3, 7, 3, 3, 6047, 3, 3, 19,
    5, 3, 17, 37, 3, 5, 11, 3, 29, 23, 3, 7, 3, 3, 7, 5, 3, 11, 19, 3, 5, 7, 3, 5, 3, 3, 19, 3, 3,
    17, 5, 3, 23, 3, 3, 5, 17, 3, 5, 11, 3, 1223, 7, 3, 41, 5, 3, 11, 3, 3, 5, 3, 3, 17, 3, 3, 7,
    3, 3, 71, 5, 3, 79, 7, 3, 5, 29, 3, 5, 13, 3, 103, 11, 3, 7, 5, 3, 7, 23, 3, 5, 31, 3, 11, 7,
    3, 43, 17, 3, 149, 5, 3, 13, 3, 3, 5, 3, 3, 7, 3, 3, 23, 3, 3, 17, 5, 3, 2801, 13, 3, 5, 3, 3,
    19, 37, 3, 11, 3, 3, 7, 5, 3, 1531, 3, 3, 5, 7, 3, 5, 43, 3, 13, 19, 3, 13, 5, 3, 7, 11, 3, 5,
    3, 3, 31, 3, 3, 11, 7, 3, 11, 5, 3, 397, 29, 3, 5, 3, 3, 5, 3, 3, 7, 3, 3, 23, 5, 3, 41, 7, 3,
    5, 11, 3, 13, 31, 3, 47, 3, 3, 7, 5, 3, 7, 3, 3, 5, 13, 3, 37, 7, 3, 59, 3, 3, 6229, 5, 3, 19,
    3, 3, 5, 3, 3, 7, 11, 3, 17, 3, 3, 13, 5, 3, 13, 3, 3, 5, 23, 3, 5, 3, 3, 7, 3, 3, 7, 5, 3, 19,
    3, 3, 5, 7, 3, 5, 3, 3, 31, 11, 3, 23, 5, 3, 7, 3, 3, 5, 19, 3, 11, 41, 3, 13, 7, 3, 19, 5, 3,
    17, 43, 3, 5, 3, 3, 5, 13, 3, 7, 31, 3, 29, 5, 3, 43, 7, 3, 5, 3, 3, 5, 3, 3, 11, 3, 3, 19, 5,
    3, 7, 3, 3, 5, 17, 3, 5, 7, 3, 31, 3, 3, 37, 5, 3, 23, 11, 3, 5, 3, 3, 7, 3, 3, 11, 3, 3, 11,
    5, 3, 47, 3, 3, 5, 3, 3, 5, 3, 3, 53, 29, 3, 7, 5, 3, 1283, 3, 3, 5, 7, 3, 5, 3, 3, 19, 13, 3,
    43, 5, 3, 11, 3, 3, 5, 3, 3, 5, 23, 3, 29, 7, 3, 17, 5, 3]

theorem certP1_ok : certOK 76550462 4 1 certP1 = true ∧ certP1.length = 738 := by
  decide +kernel

theorem prime_76547509 : Nat.Prime 76547509 := primeB_sound (by decide +kernel)

/-- p. 434: "the maximum value of `P(2n)` over the range is 2953:
`76550462 = 2953 + 76547509`", with `1` counted as a prime of the form `4k + 1`. -/
theorem noteP1_row : IsLeastP1Pair 76550462 2953 := by
  refine ⟨by norm_num, Or.inr ⟨by norm_num, by norm_num⟩,
    Or.inr ⟨by simpa using prime_76547509, by norm_num⟩, ?_⟩
  intro r hr h1 h2
  have hr4 : r % 4 = 1 := by
    rcases h1 with h | h
    · omega
    · exact h.2
  have hk : r / 4 < certP1.length := by rw [certP1_ok.2]; omega
  have := certOK_sound 76550462 4 certP1 1 certP1_ok.1 (r / 4) hk
  have e : 1 + 4 * (r / 4) = r := by omega
  rw [e] at this
  rcases this with h | h
  · rcases h1 with h1 | h1
    · omega
    · exact h.2 h1.1
  · rcases h2 with h2 | h2
    · omega
    · exact h.2 h2.1

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.certOK_sound
#print axioms LeanLab.SteinStein1965.certP_ok
#print axioms LeanLab.SteinStein1965.prime_60118819
#print axioms LeanLab.SteinStein1965.noteP_row
#print axioms LeanLab.SteinStein1965.certP1_ok
#print axioms LeanLab.SteinStein1965.prime_76547509
#print axioms LeanLab.SteinStein1965.noteP1_row

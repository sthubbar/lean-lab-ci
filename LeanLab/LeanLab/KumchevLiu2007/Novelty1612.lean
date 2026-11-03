import Mathlib
import LeanLab.KumchevLiu2007.Statements

/-!
AI wrote the Lean code, Claude, unit U-1612, run 20261103T0803Z-22341, NOVELTY triage.
Binary Goldbach is OPEN. Tag: IMPROVEMENT, a sharper exponent and an error in a printed conjecture.
Not original: the exponent is the paper's own remark, P0088 p. 3, and squares as exceptions are the
reason Hardy and Littlewood exclude them in their Conjecture H.

Source: research/novelty/KumchevLiu2007-deepseek-20261102T2137Z.md, section 4.1. The claim that
Theorem 2 holds with 0.3275 by taking θ₂ = 0.595 in Section 5 passed the numeric test
scripts/kl_sigma.py: σ₂⁻(3/5) = 0.2306 and σ₂⁺(3/5) = 2.2514 agree with the printed bounds, and at
0.595 the lower bound sum is +0.0485. It vanishes at θ₂ = 0.5934, exponent 0.3264, and is negative at
exponent 0.325, in line with the paper. The arithmetic is already `U1534.theta_thm2_improved_lt`.

`kumchev_liu_thm2_03275` is the sealed statement, CITED, the remark after Theorem 2, sorry.

Found in testing, section 5.1 of the report quotes it as a principal conjecture: P0088 p. 1 says every
sufficiently large n in H₂ is p₁ + p₂². That is FALSE as printed. `conjecture_printed_false` is
PROVED, no hypothesis: `(30 t + 6)²` is in H₂ and has no such form. `conjecture_nonsquare` is the
repaired form, OPEN. Scripts: the 13 nonsquare exceptions up to 1e8 end at 24476.
-/

namespace LeanLab.KumchevLiu2007.Novelty1612

/-- The remark after Theorem 2, p. 3: exponent 0.3275, by θ₂ = 0.595 in Section 5. -/
def kumchev_liu_thm2_03275 : Prop :=
  ShortExcBound (fun n => InH2 n ∧ ¬ IsPrimePlusPrimeSq n) (3275 / 10000)

/-- The sharper statement gives the sealed Theorem 2, so nothing is lost. -/
theorem thm2_of_03275 (h : kumchev_liu_thm2_03275) : kumchev_liu_thm2 :=
  shortExcBound_mono (by norm_num) h

/-- Vacuity: `ShortExcBound` holds for the empty predicate at this exponent, and it asks for a count
at most `C H / (log X)^A`, so it is a real upper bound with satisfiable shape. -/
theorem shortExcBound_empty : ShortExcBound (fun _ => False) (3275 / 10000) := by
  intro A _
  refine ⟨0, 0, fun X H _ _ _ => ?_⟩
  have : cntIoc (fun _ => False) X H = 0 := by
    unfold cntIoc
    simp
  simp [this]

/-- CITED, sealed target, tag IMPROVEMENT, sorry. P0088 p. 3, remark after Theorem 2. -/
theorem kumchev_liu_thm2_03275_target : kumchev_liu_thm2_03275 := by
  sorry

/-- A square in the form forces the two factors of `p = (m - q)(m + q)`. No hypothesis. -/
theorem sq_form {m : ℕ} (h : IsPrimePlusPrimeSq (m ^ 2)) :
    (m - 1).Prime ∧ (2 * m - 1).Prime := by
  obtain ⟨p, q, hp, hq, e⟩ := h
  have hq2 := hq.two_le
  have hp2 := hp.two_le
  have hqm : q < m := by
    by_contra hc
    have hc' : m ≤ q := not_lt.mp hc
    have : m ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hc' 2
    omega
  obtain ⟨d, rfl⟩ : ∃ d, m = q + d := ⟨m - q, by omega⟩
  have hd : 0 < d := by omega
  have hpd : p = d * (2 * q + d) := by
    have : (q + d) ^ 2 = d * (2 * q + d) + q ^ 2 := by ring
    omega
  have hd1 : d = 1 := by
    rcases (Nat.prime_mul_iff.mp (hpd ▸ hp)) with ⟨_, h⟩ | ⟨_, h⟩
    · omega
    · exact h
  subst hd1
  have h1 : q + 1 - 1 = q := by omega
  have h2 : 2 * (q + 1) - 1 = 2 * q + 1 := by omega
  rw [h1, h2]
  refine ⟨hq, ?_⟩
  have : p = 2 * q + 1 := by omega
  exact this ▸ hp

/-- The conjecture as printed on p. 1 of P0088. -/
def conjecture_printed : Prop := ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → InH2 n → IsPrimePlusPrimeSq n

/-- The family: `m = 30 t + 6`, `t ≥ 1`, gives `m²` in H₂. -/
theorem inH2_family (t : ℕ) : InH2 ((30 * t + 6) ^ 2) := by
  constructor
  · have : (30 * t + 6) ^ 2 = 3 * (300 * t ^ 2 + 120 * t + 12) := by ring
    omega
  · exact ⟨2 * (15 * t + 3) ^ 2, by ring⟩

theorem not_form_family {t : ℕ} (ht : 1 ≤ t) : ¬ IsPrimePlusPrimeSq ((30 * t + 6) ^ 2) := by
  intro h
  have h1 := (sq_form h).1
  have e : 30 * t + 6 - 1 = 5 * (6 * t + 1) := by omega
  rw [e] at h1
  exact Nat.not_prime_mul (by norm_num) (by omega) h1

/-- **The printed conjecture is false.** No hypothesis. -/
theorem conjecture_printed_false : ¬ conjecture_printed := by
  rintro ⟨N₀, h⟩
  have hge : N₀ ≤ (30 * (N₀ + 1) + 6) ^ 2 := by nlinarith
  exact not_form_family (Nat.succ_pos N₀) (h _ hge (inH2_family _))

/-- The repaired conjecture, OPEN. Squares removed, as in Hardy and Littlewood's Conjecture H.
A proof or a disproof is new. Vacuity: hypotheses hold at `n = 74`, `conj_hyp_74`. -/
def conjecture_nonsquare : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → InH2 n → ¬ IsSquare n → IsPrimePlusPrimeSq n

theorem conj_hyp_74 : InH2 74 ∧ ¬ IsSquare (74 : ℕ) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rintro ⟨r, hr⟩
  have : r ≤ 8 ∨ 9 ≤ r := by omega
  rcases this with h | h
  · interval_cases r <;> omega
  · nlinarith

/-- The printed conjecture implies the repaired one, the wrong way to read the repair as weakening. -/
theorem nonsquare_of_printed (h : conjecture_printed) : conjecture_nonsquare := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn h2 _ => hN n hn h2⟩

end LeanLab.KumchevLiu2007.Novelty1612

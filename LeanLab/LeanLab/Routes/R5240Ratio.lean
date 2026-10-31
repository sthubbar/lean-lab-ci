import Mathlib
import LeanLab.Common.Goldbach

/-!
# R-5240, T3 MOONSHOT: binary Goldbach as one element of a multiplicative quotient set

Unit U-6704, CLOUD 20261020T1816Z-cloud48. AI wrote this file.

Route: let `A_N` be the residues mod `N` of the primes `p < N` prime to `N`, a subset of the
unit group `G = (ZMod N)ˣ`. For `p, q` in `(0, N)`, `p * q⁻¹ = -1` in `ZMod N` iff `p + q = N`,
so binary Goldbach for `N` is the single statement `-1 ∈ A_N / A_N`, up to the case `N = 2p`.
Additive combinatorics in finite abelian groups, Kneser, Cauchy-Davenport, Plünnecke, spectral
gaps, controls only the SIZE or the expansion of `A_N / A_N`; the one size statement that
forces every class, the pigeonhole `2 |A| > |G|`, holds only for finitely many `N`.

* `zmod_add_eq_zero_iff`: for `0 < p, q < N`, `(p : ZMod N) + q = 0 ↔ p + q = N`;
* `ratio_eq_neg_one_iff`: for `q` prime to `N`, `p * q⁻¹ = -1 ↔ p + q = N` in that range;
* `goldbach_iff_neg_one_ratio`: Goldbach for `N` iff `-1` is a prime ratio mod `N`, or `N = 2p`;
* `pigeonhole_ratio`: in any finite group, `2 |A| > |G|` puts every `g` in `A * A⁻¹`.
Binary Goldbach is OPEN; this route is a reformulation and a barrier map.
-/

namespace LeanLab.Routes.R5240

/-- In `ZMod N`, two residues from `(0, N)` sum to zero exactly when the integers sum to `N`. -/
theorem zmod_add_eq_zero_iff {N p q : ℕ} (hp0 : 0 < p) (hq0 : 0 < q) (hp : p < N)
    (hq : q < N) : ((p : ZMod N) + (q : ZMod N) = 0) ↔ p + q = N := by
  constructor
  · intro h
    have h' : ((p + q : ℕ) : ZMod N) = 0 := by push_cast; exact h
    rw [ZMod.natCast_eq_zero_iff] at h'
    obtain ⟨k, hk⟩ := h'
    rcases k with _ | _ | k
    · omega
    · omega
    · nlinarith
  · intro h
    have : ((p + q : ℕ) : ZMod N) = 0 := by rw [h]; exact ZMod.natCast_self N
    push_cast at this; exact this

/-- **The ratio form.** For `q` prime to `N` and `p, q ∈ (0, N)`, `p / q = -1` in `ZMod N`
iff `p + q = N`. -/
theorem ratio_eq_neg_one_iff {N p q : ℕ} (hp0 : 0 < p) (hq0 : 0 < q) (hp : p < N)
    (hq : q < N) (hcop : q.Coprime N) :
    ((p : ZMod N) * (q : ZMod N)⁻¹ = -1) ↔ p + q = N := by
  rw [← zmod_add_eq_zero_iff hp0 hq0 hp hq]
  have hu : (q : ZMod N) * (q : ZMod N)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one q hcop
  constructor
  · intro h
    calc (p : ZMod N) + q = ((p : ZMod N) * (q : ZMod N)⁻¹ + 1) * q := by
          rw [add_mul, mul_assoc, mul_comm ((q : ZMod N)⁻¹), hu, mul_one, one_mul]
      _ = 0 := by rw [h]; ring
  · intro h
    have hp' : (p : ZMod N) = -q := eq_neg_of_add_eq_zero_left h
    rw [hp', neg_mul, hu]

/-- **Binary Goldbach for `N` as a prime ratio equal to `-1` in `ZMod N`.** Goldbach holds for
`N` iff there are primes `p, q < N`, `q` prime to `N`, with `p * q⁻¹ = -1` in `ZMod N`, or
`N = 2p` with `p` prime. -/
theorem goldbach_iff_neg_one_ratio (N : ℕ) :
    IsGoldbachSum N ↔
      (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < N ∧ q < N ∧ q.Coprime N ∧
          (p : ZMod N) * (q : ZMod N)⁻¹ = -1) ∨
        (∃ p : ℕ, p.Prime ∧ N = 2 * p) := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq⟩
    have hp2 := hp.two_le; have hq2 := hq.two_le
    by_cases hc : q.Coprime N
    · left
      exact ⟨p, q, hp, hq, by omega, by omega, hc,
        (ratio_eq_neg_one_iff (by omega) (by omega) (by omega) (by omega) hc).2 hpq⟩
    · right
      have hdvd : q ∣ N := (Nat.Prime.dvd_iff_not_coprime hq).2 hc
      have hqp : q ∣ p := by
        have : q ∣ q + p := by rw [add_comm, hpq]; exact hdvd
        exact (Nat.dvd_add_right (dvd_refl q)).1 this
      have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).1 hqp
      exact ⟨p, hp, by omega⟩
  · rintro (⟨p, q, hp, hq, hpN, hqN, hc, h⟩ | ⟨p, hp, rfl⟩)
    · exact ⟨p, q, hp, hq,
        (ratio_eq_neg_one_iff hp.pos hq.pos hpN hqN hc).1 h⟩
    · exact ⟨p, p, hp, hp, by ring⟩

/-- **Pigeonhole in a finite group.** If `2 |A| > |G|` then every `g` is a ratio `a * b⁻¹`
with `a, b ∈ A`. This is the only size statement that reaches every class; Kneser-type bounds
below it say how large `A * A⁻¹` is, never which classes it holds. -/
theorem pigeonhole_ratio {G : Type*} [Group G] [Fintype G] [DecidableEq G] (A : Finset G)
    (hA : Fintype.card G < 2 * A.card) (g : G) :
    ∃ a ∈ A, ∃ b ∈ A, a * b⁻¹ = g := by
  have hcard : (A.image (g * ·)).card = A.card :=
    Finset.card_image_of_injective _ (mul_right_injective g)
  have hne : (A ∩ A.image (g * ·)).Nonempty := by
    apply Finset.inter_nonempty_of_card_lt_card_add_card (Finset.subset_univ _)
      (Finset.subset_univ _)
    rw [Finset.card_univ, hcard]; omega
  obtain ⟨x, hx⟩ := hne
  rw [Finset.mem_inter, Finset.mem_image] at hx
  obtain ⟨hxA, b, hbA, hb⟩ := hx
  exact ⟨x, hxA, b, hbA, by rw [← hb]; group⟩

/-- Vacuity check: the hypotheses of `ratio_eq_neg_one_iff` hold at `N = 10, p = 3, q = 7`. -/
example : ((3 : ZMod 10) * (7 : ZMod 10)⁻¹ = -1) :=
  (ratio_eq_neg_one_iff (N := 10) (p := 3) (q := 7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide)).2 rfl

end LeanLab.Routes.R5240

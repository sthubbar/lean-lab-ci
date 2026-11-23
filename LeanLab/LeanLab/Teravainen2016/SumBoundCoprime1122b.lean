/-
P0076 J. Teräväinen, arXiv 1611.08585, Section 5, pages 20 to 21: the case `(q, W) = 1` of the
proof of Lemma 5.3. The decomposition `c₀ = c₁ q + c₂ Q' (mod Q)` of display (5.10) is a bijection
from `(ℤ/q'Q') × (ℤ/q)` onto `ℤ/Q`; under it the set `𝒬` of display (5.1) is the product of a
`c₁` set and the `c₂` set `QRes q (W Q') b`, the phase depends on `c₂` alone, and the `c₂` sum is
the sum of Lemma 5.4, display (5.5), bounded by `τ(q)` in `SieveResidues`.
AI wrote this Lean code, Claude, session CLOUD-S69. Checked only by the Lean kernel.
The binary Goldbach conjecture is OPEN.
-/
import LeanLab.Teravainen2016.Lemma53Split
import LeanLab.Teravainen2016.SieveResidues

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016.Lemma53Split

open LeanLab.Teravainen2016

/-- Membership in `QRes`, display (5.1), written prime by prime. -/
theorem mem_QRes_iff_1122b {Q : ℕ} (hQ : Q ≠ 0) (W b : ℤ) (c : ℕ) :
    c ∈ QRes Q W b ↔ c < Q ∧ ∀ p : ℕ, p.Prime → p ∣ Q →
      ¬ (p : ℤ) ∣ W * c + b ∧ (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ W * c + b - 1) := by
  simp only [QRes, mem_filter, mem_range, int_coprime_primeFactors_iff hQ, Nat.mem_primeFactors]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, fun p hp hpQ => ⟨h1 p ⟨hp, hpQ, hQ⟩, fun h4 h3 => h2 p hp h4 h3 hpQ⟩⟩
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun p ⟨hp, hpQ, _⟩ => (h p hp hpQ).1, fun p hp h4 h3 hpQ => (h p hp hpQ).2 h4 h3⟩

/-- The prime by prime sieve condition at `M` depends on `x` only through its residues modulo the
primes of `M`. -/
theorem cond_congr_1122b (M : ℕ) (x y : ℤ)
    (h : ∀ p : ℕ, p.Prime → p ∣ M → (p : ℤ) ∣ x - y) :
    (∀ p : ℕ, p.Prime → p ∣ M → ¬ (p : ℤ) ∣ x ∧ (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ x - 1)) ↔
    (∀ p : ℕ, p.Prime → p ∣ M → ¬ (p : ℤ) ∣ y ∧ (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ y - 1)) := by
  have key : ∀ p : ℕ, p.Prime → p ∣ M →
      (((p : ℤ) ∣ x ↔ (p : ℤ) ∣ y) ∧ ((p : ℤ) ∣ x - 1 ↔ (p : ℤ) ∣ y - 1)) := by
    intro p hp hpM
    have hd := h p hp hpM
    refine ⟨⟨fun hx => ?_, fun hy => ?_⟩, ⟨fun hx => ?_, fun hy => ?_⟩⟩
    · have e : y = x - (x - y) := by ring
      rw [e]; exact dvd_sub hx hd
    · have e : x = y + (x - y) := by ring
      rw [e]; exact dvd_add hy hd
    · have e : y - 1 = (x - 1) - (x - y) := by ring
      rw [e]; exact dvd_sub hx hd
    · have e : x - 1 = (y - 1) + (x - y) := by ring
      rw [e]; exact dvd_add hy hd
  constructor
  · intro hx p hp hpM
    obtain ⟨k1, k2⟩ := key p hp hpM
    exact ⟨fun hy => (hx p hp hpM).1 (k1.mpr hy), fun h4 h3 hy => (hx p hp hpM).2 h4 h3 (k2.mpr hy)⟩
  · intro hy p hp hpM
    obtain ⟨k1, k2⟩ := key p hp hpM
    exact ⟨fun hx => (hy p hp hpM).1 (k1.mp hx), fun h4 h3 hx => (hy p hp hpM).2 h4 h3 (k2.mp hx)⟩

/-- For `Q = q q' Q'` with every prime of `q'` dividing `q`, the condition at `Q` is the
conjunction of the conditions at `q` and at `Q'`. -/
theorem cond_split_1122b (q q' Q' : ℕ) (hq' : ∀ p : ℕ, p.Prime → p ∣ q' → p ∣ q) (x : ℤ) :
    (∀ p : ℕ, p.Prime → p ∣ q * q' * Q' →
      ¬ (p : ℤ) ∣ x ∧ (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ x - 1)) ↔
    (∀ p : ℕ, p.Prime → p ∣ q →
      ¬ (p : ℤ) ∣ x ∧ (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ x - 1)) ∧
    (∀ p : ℕ, p.Prime → p ∣ Q' →
      ¬ (p : ℤ) ∣ x ∧ (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ x - 1)) := by
  constructor
  · intro h
    exact ⟨fun p hp hpq => h p hp (Dvd.dvd.mul_right (Dvd.dvd.mul_right hpq _) _),
      fun p hp hpQ => h p hp (Dvd.dvd.mul_left hpQ _)⟩
  · rintro ⟨h1, h2⟩ p hp hpd
    rcases hp.dvd_mul.mp hpd with h | h
    · rcases hp.dvd_mul.mp h with h' | h'
      · exact h1 p hp h'
      · exact h1 p hp (hq' p hp h')
    · exact h2 p hp h

/-- Pages 20 to 21: every `m ≥ 1` is `q' Q'` with `(Q', q) = 1` and every prime of `q'` dividing
`q`. -/
theorem exists_split_1122b (q : ℕ) : ∀ m : ℕ, m ≠ 0 →
    ∃ q' Q' : ℕ, m = q' * Q' ∧ Q'.Coprime q ∧ ∀ p : ℕ, p.Prime → p ∣ q' → p ∣ q := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm
  by_cases h : ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ p ∣ q
  · obtain ⟨p, hp, hpm, hpq⟩ := h
    obtain ⟨m1, rfl⟩ := hpm
    have hm1 : m1 ≠ 0 := by rintro rfl; simp at hm
    have hlt : m1 < p * m1 := by
      have := hp.one_lt
      have := Nat.pos_of_ne_zero hm1
      nlinarith
    obtain ⟨q1, Q1, h1, h2, h3⟩ := ih m1 hlt hm1
    refine ⟨p * q1, Q1, by rw [h1]; ring, h2, ?_⟩
    intro r hr hrd
    rcases hr.dvd_mul.mp hrd with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hr hp).mp h]; exact hpq
    · exact h3 r hr h
  · refine ⟨1, m, by ring, ?_, ?_⟩
    · apply Nat.coprime_of_dvd
      intro p hp hpm hpq
      exact h ⟨p, hp, hpm, hpq⟩
    · intro p hp hp1
      have := Nat.le_of_dvd one_pos hp1
      have := hp.two_le
      omega

/-- Display (5.10): `(c₁, c₂) ↦ c₁ q + c₂ Q' (mod q q' Q')` is injective on
`[0, q'Q') × [0, q)` when `(q, Q') = 1`. -/
theorem decomp_injOn_1122b (q q' Q' : ℕ) (hq0 : q ≠ 0) (hQ'q : Q'.Coprime q) :
    Set.InjOn (fun c : ℕ × ℕ => (c.1 * q + c.2 * Q') % (q * q' * Q'))
      ((range (q' * Q') ×ˢ range q : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
  rintro ⟨c1, c2⟩ hc ⟨d1, d2⟩ hd h
  simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio] at hc hd
  simp only at h
  have hmod : c1 * q + c2 * Q' ≡ d1 * q + d2 * Q' [MOD q * q' * Q'] := h
  have hdv := (Nat.modEq_iff_dvd.mp hmod)
  push_cast at hdv
  have hcop : IsCoprime (q : ℤ) (Q' : ℤ) := Nat.isCoprime_iff_coprime.mpr hQ'q.symm
  have hq2 : (q : ℤ) ∣ ((d2 : ℤ) - c2) * Q' := by
    have h1 : (q : ℤ) ∣ (d1 * q + d2 * Q' : ℤ) - (c1 * q + c2 * Q') :=
      (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl (q : ℤ)) _) _).trans hdv
    have e : ((d2 : ℤ) - c2) * Q' = ((d1 * q + d2 * Q' : ℤ) - (c1 * q + c2 * Q')) - (q : ℤ) * (d1 - c1) := by
      ring
    rw [e]; exact dvd_sub h1 (Dvd.intro _ rfl)
  have hq2' : (q : ℤ) ∣ (d2 : ℤ) - c2 := hcop.dvd_of_dvd_mul_right hq2
  have h2eq : (d2 : ℤ) - c2 = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd hq2'
    rw [abs_sub_lt_iff]; constructor <;> omega
  have h2 : c2 = d2 := by omega
  subst h2
  have hNpos : 0 < q' * Q' := by
    rcases Nat.eq_zero_or_pos (q' * Q') with h0 | h0
    · rw [h0] at hc; exact absurd hc.1 (Nat.not_lt_zero _)
    · exact h0
  have hdv2 : ((q' * Q' : ℕ) : ℤ) * q ∣ ((d1 : ℤ) - c1) * q := by
    have e : ((d1 : ℤ) - c1) * q = (d1 * q + c2 * Q' : ℤ) - (c1 * q + c2 * Q') := by ring
    rw [e]
    have e2 : ((q' * Q' : ℕ) : ℤ) * q = (q : ℤ) * q' * Q' := by push_cast; ring
    rw [e2]; exact hdv
  have hq0' : (q : ℤ) ≠ 0 := by exact_mod_cast hq0
  have hdv3 : ((q' * Q' : ℕ) : ℤ) ∣ (d1 : ℤ) - c1 := (mul_dvd_mul_iff_right hq0').mp hdv2
  have h1eq : (d1 : ℤ) - c1 = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd hdv3
    generalize q' * Q' = N at hc hd hNpos
    rw [abs_sub_lt_iff]; constructor <;> omega
  have h1 : c1 = d1 := by omega
  rw [h1]

/-- The integer form of the reduced representative. -/
theorem decomp_cast_1122b (x Q : ℕ) :
    ((x % Q : ℕ) : ℤ) = x - Q * ((x / Q : ℕ) : ℤ) := by
  have := Nat.mod_add_div x Q
  have h2 : ((x % Q : ℕ) : ℤ) + Q * ((x / Q : ℕ) : ℤ) = x := by exact_mod_cast this
  linarith

/-- The `c₂` sum of display (5.5) as `QRes q (W Q') b`. -/
theorem QRes_eq_integer_filter_1122b {q : ℕ} (hq0 : q ≠ 0) (W V b : ℤ) :
    QRes q (W * V) b = (range q).filter (fun n : ℕ => IsCoprime (W * V * n + b) (q : ℤ) ∧
      (∀ p ∈ q.primeFactors, p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ W * V * n + b - 1)) := by
  unfold QRes
  apply filter_congr
  intro n _
  simp only [Nat.mem_primeFactors]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun p ⟨hp, hpq, _⟩ h4 h3 => h2 p hp h4 h3 hpq⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun p hp h4 h3 hpq => h2 p ⟨hp, hpq, hq0⟩ h4 h3⟩

/-- Pages 20 to 21, for any `W`: with `Q = q q' Q'`, `(Q', q) = 1` and every prime of `q'`
dividing `q`, display (5.10) factors `Σ_{c₀ ∈ 𝒬} e(a c₀/q)` as `#𝒬₁ · S` with `S` the sum of
display (5.5) at `V = Q'` and frequency `a Q'`, and `#𝒬 = #𝒬₁ · #QRes q (W Q') b`. -/
theorem sum_bound_split_general_1122b (W b : ℤ) (q q' Q' a : ℕ) (hq0 : q ≠ 0)
    (hQ'0 : q' * Q' ≠ 0) (hQ'q : Q'.Coprime q) (hq' : ∀ p : ℕ, p.Prime → p ∣ q' → p ∣ q)
    (haq : a.Coprime q) :
    ‖∑ c₀ ∈ QRes (q * q' * Q') W b, eC ((a : ℝ) * c₀ / q)‖ * #(QRes q (W * Q') b) ≤
      (q.divisors.card : ℝ) * #(QRes (q * q' * Q') W b) := by
  haveI : NeZero q := ⟨hq0⟩
  set Q := q * q' * Q' with hQdef
  have hQ0 : Q ≠ 0 := by
    rw [hQdef, mul_assoc]; exact mul_ne_zero hq0 hQ'0
  have hQ'ne : Q' ≠ 0 := by rintro rfl; simp at hQ'0
  set N := q' * Q' with hN
  set φ : ℕ × ℕ → ℕ := fun c => (c.1 * q + c.2 * Q') % Q with hφ
  set A1 : Finset ℕ := (range N).filter (fun c1 => ∀ p : ℕ, p.Prime → p ∣ Q' →
      ¬ (p : ℤ) ∣ W * ((q : ℤ) * c1) + b ∧
        (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ W * ((q : ℤ) * c1) + b - 1)) with hA1
  set A2 : Finset ℕ := QRes q (W * Q') b with hA2
  have hinj : Set.InjOn φ ((range N ×ˢ range q : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) :=
    decomp_injOn_1122b q q' Q' hq0 hQ'q
  have hrange : (range N ×ˢ range q).image φ = range Q := by
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨c, -, rfl⟩ := mem_image.mp hx
      exact mem_range.mpr (Nat.mod_lt _ (Nat.pos_of_ne_zero hQ0))
    · rw [card_image_of_injOn hinj, card_product, card_range, card_range, card_range, hN, hQdef]
      apply le_of_eq; ring
  -- the shifts behind (5.10)
  have hcast : ∀ c : ℕ × ℕ, ((φ c : ℕ) : ℤ) =
      c.1 * q + c.2 * Q' - Q * (((c.1 * q + c.2 * Q') / Q : ℕ) : ℤ) := by
    intro c
    simp only [hφ]
    rw [decomp_cast_1122b]; push_cast; ring
  have hmem : ∀ c : ℕ × ℕ, c ∈ range N ×ˢ range q → (φ c ∈ QRes Q W b ↔ c.1 ∈ A1 ∧ c.2 ∈ A2) := by
    rintro ⟨c1, c2⟩ hc
    simp only [mem_product, mem_range] at hc
    rw [mem_QRes_iff_1122b hQ0, hA2, mem_QRes_iff_1122b hq0, hA1, mem_filter, mem_range]
    have hlt : φ (c1, c2) < Q := Nat.mod_lt _ (Nat.pos_of_ne_zero hQ0)
    have hc' := hcast (c1, c2)
    simp only at hc'
    generalize (((c1 * q + c2 * Q') / Q : ℕ) : ℤ) = k at hc'
    rw [hQdef, cond_split_1122b q q' Q' hq']
    rw [← hQdef]
    have e1 : ∀ p : ℕ, p.Prime → p ∣ q →
        (p : ℤ) ∣ (W * ((φ (c1, c2) : ℕ) : ℤ) + b) - (W * Q' * c2 + b) := by
      intro p _ hpq
      have e : (W * ((φ (c1, c2) : ℕ) : ℤ) + b) - (W * Q' * c2 + b) =
          (q : ℤ) * (W * c1 - W * q' * Q' * k) := by
        rw [hc', hQdef]; push_cast; ring
      rw [e]; exact (Int.natCast_dvd_natCast.mpr hpq).mul_right _
    have e2 : ∀ p : ℕ, p.Prime → p ∣ Q' →
        (p : ℤ) ∣ (W * ((φ (c1, c2) : ℕ) : ℤ) + b) - (W * ((q : ℤ) * c1) + b) := by
      intro p _ hpQ
      have e : (W * ((φ (c1, c2) : ℕ) : ℤ) + b) - (W * ((q : ℤ) * c1) + b) =
          (Q' : ℤ) * (W * c2 - W * q * q' * k) := by
        rw [hc', hQdef]; push_cast; ring
      rw [e]; exact (Int.natCast_dvd_natCast.mpr hpQ).mul_right _
    rw [cond_congr_1122b q _ _ e1, cond_congr_1122b Q' _ _ e2]
    tauto
  -- the phase depends on `c₂` alone
  have hphase : ∀ c : ℕ × ℕ, eC ((a : ℝ) * (φ c : ℕ) / q) =
      eC (((a * Q' : ℕ) : ℝ) * (c.2 : ℕ) / q) := by
    intro c
    have h1 : ((φ c : ℕ) : ℝ) = c.1 * q + c.2 * Q' - q * q' * Q' * (((c.1 * q + c.2 * Q') / Q : ℕ) : ℝ) := by
      have := hcast c
      rw [hQdef] at this
      exact_mod_cast this
    have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
    have h2 : (a : ℝ) * (φ c : ℕ) / q = ((a * Q' : ℕ) : ℝ) * (c.2 : ℕ) / q +
        (((a * c.1 : ℕ) : ℤ) - ((a * q' * Q' * ((c.1 * q + c.2 * Q') / Q) : ℕ) : ℤ) : ℤ) := by
      generalize ((c.1 * q + c.2 * Q') / Q) = k at h1 ⊢
      rw [h1]; push_cast; field_simp; ring
    rw [h2, eC_add_l, eC_int_l, mul_one]
  -- the set `𝒬` is the image of `A1 × A2`
  have hΨ : QRes Q W b = (A1 ×ˢ A2).image φ := by
    ext x
    constructor
    · intro hx
      have hxQ : x ∈ range Q := by
        simp only [QRes, mem_filter] at hx; exact hx.1
      rw [← hrange] at hxQ
      obtain ⟨c, hc, rfl⟩ := mem_image.mp hxQ
      exact mem_image.mpr ⟨c, mem_product.mpr ((hmem c hc).mp hx), rfl⟩
    · intro hx
      obtain ⟨c, hc, rfl⟩ := mem_image.mp hx
      have hc' : c ∈ range N ×ˢ range q := by
        rw [mem_product] at hc ⊢
        refine ⟨(mem_filter.mp hc.1).1, ?_⟩
        have := hc.2
        rw [hA2, mem_QRes_iff_1122b hq0] at this
        exact mem_range.mpr this.1
      exact (hmem c hc').mpr (mem_product.mp hc)
  have hsub : A1 ×ˢ A2 ⊆ range N ×ˢ range q := by
    intro c hc
    rw [mem_product] at hc ⊢
    refine ⟨(mem_filter.mp hc.1).1, ?_⟩
    have := hc.2
    rw [hA2, mem_QRes_iff_1122b hq0] at this
    exact mem_range.mpr this.1
  have hinj' : Set.InjOn φ ((A1 ×ˢ A2 : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) :=
    hinj.mono (by exact_mod_cast hsub)
  set S : ℂ := ∑ c₂ ∈ A2, eC (((a * Q' : ℕ) : ℝ) * (c₂ : ℕ) / q) with hS
  have hsum : ∑ c₀ ∈ QRes Q W b, eC ((a : ℝ) * c₀ / q) = (#A1 : ℂ) * S := by
    rw [hΨ, sum_image hinj', sum_product]
    simp_rw [hphase]
    rw [sum_const, nsmul_eq_mul]
  have hcard : #(QRes Q W b) = #A1 * #A2 := by
    rw [hΨ, card_image_of_injOn hinj', card_product]
  have hSle : ‖S‖ ≤ (q.divisors.card : ℝ) := by
    have h := integerSieveSum_norm_le_divisors q W Q' b (a * Q') (Nat.coprime_mul_iff_left.mpr ⟨haq, hQ'q⟩)
    have heq : S = integerSieveSum q W Q' b (a * Q') := by
      rw [hS, hA2, QRes_eq_integer_filter_1122b hq0]
      rfl
    rw [heq]; exact h
  rw [hsum, hcard, norm_mul, Complex.norm_natCast]
  push_cast
  have h0 : (0 : ℝ) ≤ #A1 := Nat.cast_nonneg _
  have h0' : (0 : ℝ) ≤ #A2 := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hSle h0
  have := mul_le_mul_of_nonneg_right this h0'
  nlinarith

/-- Lemma 5.3, pages 20 to 21, the case `(q, W) = 1`, proved: the exact statement of the LEAF
`Lemma53Split.sum_bound_of_coprime`. -/
theorem sum_bound_of_coprime_proved (J w : ℕ) (hJ : 5 ≤ J) (hw : wBig ≤ w) (b : ℤ)
    (hb : Amenable (WW J w) b) (Q q a : ℕ) (hQ : 1 ≤ Q) (hqQ : q ∣ Q) (hq1 : q ≠ 1)
    (ha : 0 < a) (haq : a.Coprime q) (hqW : IsCoprime (q : ℤ) (WW J w)) :
    ∃ q' Q' : ℕ, Q = q * q' * Q' ∧ Q'.Coprime q ∧ (∀ p : ℕ, p.Prime → p ∣ q' → p ∣ q) ∧
      ‖∑ c₀ ∈ QRes Q (WW J w) b, eC ((a : ℝ) * c₀ / q)‖ *
          #(QRes q (WW J w * Q') b) ≤
        (q.divisors.card : ℝ) * #(QRes Q (WW J w) b) := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hqQ
    omega
  obtain ⟨m, hm⟩ := hqQ
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
    omega
  obtain ⟨q', Q', h1, h2, h3⟩ := exists_split_1122b q m hm0
  have hQe : Q = q * q' * Q' := by rw [hm, h1]; ring
  refine ⟨q', Q', hQe, h2, h3, ?_⟩
  rw [hQe]
  exact sum_bound_split_general_1122b (WW J w) b q q' Q' a hq0 (by rw [← h1]; exact hm0) h2 h3 haq

/-- Twin check: the proved theorem has, up to definitional equality, the type of the LEAF. -/
theorem sum_bound_of_coprime_twin : type_of% @sum_bound_of_coprime :=
  sum_bound_of_coprime_proved

end LeanLab.Teravainen2016.Lemma53Split

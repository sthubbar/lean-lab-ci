/-
P0076 J. Teräväinen, arXiv 1611.08585, Section 5, pages 19 to 21: Lemma 5.3, display (5.4),
split along the printed proof into the decomposition (5.10) with Lemma 5.4, the divisor bound,
and the local density of the residue set modulo `q`.
AI wrote this Lean code, Claude, session CLOUD-S62. Checked only by the Lean kernel.
The binary Goldbach conjecture is OPEN.
-/
import LeanLab.Teravainen2016.WeightedPrimeSplit
import LeanLab.Teravainen2016.RoughDivisors
import LeanLab.Teravainen2016.SieveResidues

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016.Lemma53Split

open LeanLab.Teravainen2016

/-- `e(x + y) = e(x) e(y)`. -/
theorem eC_add_l (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- `e(m) = 1` for integers `m`. -/
theorem eC_int_l (m : ℤ) : eC (m : ℝ) = 1 := by
  unfold eC
  rw [Complex.exp_eq_one_iff]
  exact ⟨m, by push_cast; ring⟩

/-- `e(x) = 1` exactly at the integers. -/
theorem eC_eq_one_iff_l (x : ℝ) : eC x = 1 ↔ ∃ m : ℤ, x = m := by
  unfold eC
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h : (2 * Real.pi * Complex.I) * (x : ℂ) = (2 * Real.pi * Complex.I) * (n : ℂ) := by
      rw [hn]; ring
    have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have := mul_left_cancel₀ hne h
    exact_mod_cast this
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; ring⟩

/-- Coprimality to `Q` survives a shift divisible by every prime of `Q`. -/
theorem isCoprime_shift (x y : ℤ) (Q : ℕ)
    (hy : ∀ r : ℕ, r.Prime → r ∣ Q → (r : ℤ) ∣ y) (hx : IsCoprime x Q) :
    IsCoprime (x + y) Q := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
  apply Nat.coprime_of_dvd
  intro r hr h1 h2
  have hrQ : r ∣ Q := by simpa using h2
  have h1' : (r : ℤ) ∣ x + y := Int.ofNat_dvd_left.mpr h1
  have hrx : (r : ℤ) ∣ x := by
    have := dvd_sub h1' (hy r hr hrQ); simpa using this
  have hrQ' : (r : ℤ) ∣ (Q : ℤ) := by exact_mod_cast hrQ
  have hu := hx.isUnit_of_dvd' hrx hrQ'
  rw [Int.isUnit_iff_natAbs_eq] at hu
  simp at hu
  exact hr.one_lt.ne' hu

/-- Non divisibility by `p ∣ Q` survives a shift divisible by every prime of `Q`. -/
theorem not_dvd_shift (x y : ℤ) (Q p : ℕ) (hpQ : p ∣ Q)
    (hy : ∀ r : ℕ, r.Prime → r ∣ Q → (r : ℤ) ∣ y) (hp : p.Prime) (hx : ¬ (p : ℤ) ∣ x) :
    ¬ (p : ℤ) ∣ x + y := by
  intro h
  apply hx
  have := dvd_sub h (hy p hp hpQ); simpa using this

/-- The case `(q, W) > 1` of Lemma 5.3, pages 19 to 20, for any `W`. The paper gets it from
(5.10) and the vanishing case of Lemma 5.4; here the same fact is proved directly: for a prime
`p ∣ q`, `p ∣ W`, the shift `c₀ ↦ c₀ + t (mod Q)` with `t = ∏_{r ∣ Q, r ≠ p} r` preserves `𝒬`,
since `W t` is divisible by every prime of `Q`, and multiplies the phase by `e(a t/q) ≠ 1`. -/
theorem sum_eq_zero_of_not_coprime_general (W : ℤ) (b : ℤ)
    (Q q a : ℕ) (hQ : 1 ≤ Q) (hqQ : q ∣ Q) (haq : a.Coprime q)
    (hqW : ¬ IsCoprime (q : ℤ) W) :
    ∑ c₀ ∈ QRes Q W b, eC ((a : ℝ) * c₀ / q) = 0 := by
  rw [Int.isCoprime_iff_gcd_eq_one] at hqW
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hqW
  have hpdi : (p : ℤ) ∣ (Int.gcd (q : ℤ) W : ℤ) := by exact_mod_cast hpd
  have hpq : p ∣ q := by
    have := hpdi.trans (Int.gcd_dvd_left (a := (q : ℤ)) (b := W))
    exact_mod_cast this
  have hpW : (p : ℤ) ∣ W := hpdi.trans (Int.gcd_dvd_right (a := (q : ℤ)) (b := W))
  have hpQ : p ∣ Q := hpq.trans hqQ
  have hQ0 : Q ≠ 0 := by omega
  have hq0 : q ≠ 0 := by rintro rfl; simp at hqQ; omega
  obtain ⟨m, hm⟩ := hqQ
  set t : ℕ := ∏ r ∈ Q.primeFactors.erase p, r with ht
  have hWt : ∀ r : ℕ, r.Prime → r ∣ Q → (r : ℤ) ∣ W * t := by
    intro r hr hrQ
    by_cases hrp : r = p
    · subst hrp; exact hpW.mul_right _
    · apply Dvd.dvd.mul_left
      have : r ∣ t := dvd_prod_of_mem _ (mem_erase.mpr ⟨hrp, Nat.mem_primeFactors.mpr ⟨hr, hrQ, hQ0⟩⟩)
      exact_mod_cast this
  have hpt : ¬ p ∣ t := by
    rw [ht, (Nat.Prime.prime hp).dvd_finsetProd_iff]
    rintro ⟨r, hr, hpr⟩
    obtain ⟨hrp, hrm⟩ := mem_erase.mp hr
    have hrpr := Nat.prime_of_mem_primeFactors hrm
    exact hrp ((Nat.prime_dvd_prime_iff_eq hp hrpr).mp hpr).symm
  set f : ℕ → ℕ := fun c => (c + t) % Q with hf
  -- the shift as an integer identity
  have hcast : ∀ c : ℕ, ((f c : ℕ) : ℤ) = c + t - Q * (((c + t) / Q : ℕ) : ℤ) := by
    intro c
    have := Nat.mod_add_div (c + t) Q
    simp only [hf]
    have h2 : (((c + t) % Q : ℕ) : ℤ) + Q * (((c + t) / Q : ℕ) : ℤ) = c + t := by exact_mod_cast this
    linarith
  have hy : ∀ c : ℕ, ∀ r : ℕ, r.Prime → r ∣ Q →
      (r : ℤ) ∣ W * t - W * Q * (((c + t) / Q : ℕ) : ℤ) := by
    intro c r hr hrQ
    apply dvd_sub (hWt r hr hrQ)
    have : (r : ℤ) ∣ (Q : ℤ) := by exact_mod_cast hrQ
    exact (this.mul_left W).mul_right _
  have hmaps : ∀ c ∈ QRes Q W b, f c ∈ QRes Q W b := by
    intro c hc
    simp only [QRes, mem_filter, mem_range] at hc ⊢
    obtain ⟨-, hc1, hc2⟩ := hc
    have hid : W * ((f c : ℕ) : ℤ) + b = (W * c + b) + (W * t - W * Q * (((c + t) / Q : ℕ) : ℤ)) := by
      rw [hcast]; ring
    refine ⟨Nat.mod_lt _ (by omega), ?_, ?_⟩
    · rw [hid]; exact isCoprime_shift _ _ Q (hy c) hc1
    · intro r hr h4 h3 hrQ
      have hid' : W * ((f c : ℕ) : ℤ) + b - 1 =
          (W * c + b - 1) + (W * t - W * Q * (((c + t) / Q : ℕ) : ℤ)) := by rw [hid]; ring
      rw [hid']
      exact not_dvd_shift _ _ Q r hrQ (hy c) hr (hc2 r hr h4 h3 hrQ)
  have hinj : Set.InjOn f (QRes Q W b) := by
    intro c1 h1 c2 h2 h
    simp only [QRes, coe_filter, mem_range, Set.mem_ofPred_eq] at h1 h2
    have hmod : c1 ≡ c2 [MOD Q] := Nat.ModEq.add_right_cancel' t h
    have := hmod
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt h1.1, Nat.mod_eq_of_lt h2.1] at this
  have himage : (QRes Q W b).image f = QRes Q W b := by
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := mem_image.mp hx
      exact hmaps c hc
    · rw [card_image_of_injOn hinj]
  -- the phase
  set e : ℂ := eC ((a : ℝ) * t / q) with he
  have hshift : ∀ c : ℕ, eC ((a : ℝ) * (f c : ℕ) / q) = eC ((a : ℝ) * c / q) * e := by
    intro c
    have h1 : ((f c : ℕ) : ℝ) = c + t - Q * (((c + t) / Q : ℕ) : ℝ) := by
      have := hcast c
      exact_mod_cast this
    have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
    have h2 : (a : ℝ) * (f c : ℕ) / q =
        ((a : ℝ) * c / q + (a : ℝ) * t / q) + ((-(a * m * ((c + t) / Q) : ℕ) : ℤ) : ℝ) := by
      generalize (c + t) / Q = k at h1 ⊢
      rw [h1, hm]; push_cast; field_simp; ring
    rw [h2, eC_add_l, eC_int_l, mul_one, eC_add_l]
  have hsum : ∑ c₀ ∈ QRes Q W b, eC ((a : ℝ) * c₀ / q) =
      (∑ c₀ ∈ QRes Q W b, eC ((a : ℝ) * c₀ / q)) * e := by
    conv_lhs => rw [← himage]
    rw [sum_image hinj, sum_mul]
    exact sum_congr rfl (fun c _ => hshift c)
  have hene : e ≠ 1 := by
    rw [he, Ne, eC_eq_one_iff_l]
    rintro ⟨k, hk⟩
    have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
    have h3 : ((a * t : ℕ) : ℤ) = (q : ℤ) * k := by
      have : ((a : ℝ) * t) = q * k := by field_simp at hk; linarith
      exact_mod_cast this
    have hpat : (p : ℤ) ∣ ((a * t : ℕ) : ℤ) := by
      rw [h3]; exact (Int.natCast_dvd_natCast.mpr hpq).mul_right _
    have hpat' : p ∣ a * t := by exact_mod_cast hpat
    rcases (Nat.Prime.dvd_mul hp).mp hpat' with hpa | hpt'
    · have := Nat.dvd_gcd hpa hpq
      rw [haq] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    · exact hpt hpt'
  have hz : (∑ c₀ ∈ QRes Q W b, eC ((a : ℝ) * c₀ / q)) * (e - 1) = 0 := by
    rw [mul_sub, mul_one, ← hsum, sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hene

/-- Lemma 5.3, page 20, the case `(q, W) > 1`: the left side of (5.4) vanishes. -/
theorem sum_eq_zero_of_not_coprime (J w : ℕ) (b : ℤ) (Q q a : ℕ) (hQ : 1 ≤ Q) (hqQ : q ∣ Q)
    (haq : a.Coprime q) (hqW : ¬ IsCoprime (q : ℤ) (WW J w)) :
    ∑ c₀ ∈ QRes Q (WW J w) b, eC ((a : ℝ) * c₀ / q) = 0 :=
  sum_eq_zero_of_not_coprime_general (WW J w) b Q q a hQ hqQ haq hqW

/-- Membership in `QRes`, display (5.1), written prime by prime. -/
private theorem mem_QRes_iff_1122b {Q : ℕ} (hQ : Q ≠ 0) (W b : ℤ) (c : ℕ) :
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
private theorem cond_congr_1122b (M : ℕ) (x y : ℤ)
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
private theorem cond_split_1122b (q q' Q' : ℕ) (hq' : ∀ p : ℕ, p.Prime → p ∣ q' → p ∣ q) (x : ℤ) :
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
private theorem exists_split_1122b (q : ℕ) : ∀ m : ℕ, m ≠ 0 →
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
private theorem decomp_injOn_1122b (q q' Q' : ℕ) (hq0 : q ≠ 0) (hQ'q : Q'.Coprime q) :
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
private theorem decomp_cast_1122b (x Q : ℕ) :
    ((x % Q : ℕ) : ℤ) = x - Q * ((x / Q : ℕ) : ℤ) := by
  have := Nat.mod_add_div x Q
  have h2 : ((x % Q : ℕ) : ℤ) + Q * ((x / Q : ℕ) : ℤ) = x := by exact_mod_cast this
  linarith

/-- The `c₂` sum of display (5.5) as `QRes q (W Q') b`. -/
private theorem QRes_eq_integer_filter_1122b {q : ℕ} (hq0 : q ≠ 0) (W V b : ℤ) :
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
private theorem sum_bound_split_general_1122b (W b : ℤ) (q q' Q' a : ℕ) (hq0 : q ≠ 0)
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

/-- LEAF: proof of Lemma 5.3, pages 20 to 21, the case `(q, W) = 1`. Class MEDIUM. With
`Q = q q' Q'`, `(q, Q') = 1` and every prime of `q'` dividing `q`, the decomposition
`c₀ = c₁ q + c₂ Q'` of display (5.10) and Lemma 5.4, display (5.5), give
`|Σ| ≤ τ(q) · #{c₁ (mod q' Q')}`, and the same decomposition splits `𝒬` as the product of the
`c₁` set and the `c₂` set `{c₂ (mod q) : (W Q' c₂ + b, q) = (W Q' c₂ + b - 1, s(q)) = 1}`,
which is `QRes q (W Q') b`. Multiplying through by the size of the `c₂` set gives the bound. -/
theorem sum_bound_of_coprime (J w : ℕ) (hJ : 5 ≤ J) (hw : wBig ≤ w) (b : ℤ)
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

/-- Divisibility of a linear form by a prime depends only on the argument modulo a multiple
of that prime. -/
private theorem dvd_iff_dvd_mod (K b : ℤ) {d p : ℕ} (hpd : p ∣ d) (c : ℕ) :
    ((p : ℤ) ∣ K * (c : ℤ) + b) ↔ ((p : ℤ) ∣ K * ((c % d : ℕ) : ℤ) + b) := by
  have hsum : ((c % d : ℕ) : ℤ) + ((d * (c / d) : ℕ) : ℤ) = (c : ℤ) := by
    rw [← Nat.cast_add, Nat.mod_add_div]
  have hdec : (c : ℤ) = ((c % d : ℕ) : ℤ) + (d : ℤ) * ((c / d : ℕ) : ℤ) := by
    rw [← hsum, Nat.cast_mul]
  have hpd' : (p : ℤ) ∣ (d : ℤ) := by exact_mod_cast hpd
  have hK : (p : ℤ) ∣ K * ((d : ℤ) * ((c / d : ℕ) : ℤ)) :=
    (hpd'.mul_right ((c / d : ℕ) : ℤ)).mul_left K
  have hsplit : K * (c : ℤ) + b
      = (K * ((c % d : ℕ) : ℤ) + b) + K * ((d : ℤ) * ((c / d : ℕ) : ℤ)) := by
    rw [hdec]; ring
  constructor
  · intro h
    have h2 := dvd_sub h hK
    rwa [hsplit, add_sub_cancel_right] at h2
  · intro h
    rw [hsplit]
    exact dvd_add h hK

/-- The local condition of display (5.1) at a prime `p` depends only on the argument modulo
any multiple of `p`. -/
private theorem cond_iff_cond_mod (K b : ℤ) {d p c : ℕ} (hpd : p ∣ d) :
    ((¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
        (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1)) ↔
      (¬ (p : ℤ) ∣ K * ((c % d : ℕ) : ℤ) + b ∧
        (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * ((c % d : ℕ) : ℤ) + b - 1))) := by
  have h1 : ((p : ℤ) ∣ K * (c : ℤ) + b) ↔ ((p : ℤ) ∣ K * ((c % d : ℕ) : ℤ) + b) :=
    dvd_iff_dvd_mod K b hpd c
  have h2 : ((p : ℤ) ∣ K * (c : ℤ) + b - 1) ↔
      ((p : ℤ) ∣ K * ((c % d : ℕ) : ℤ) + b - 1) := by
    have h := dvd_iff_dvd_mod K (b - 1) hpd c
    have e1 : K * (c : ℤ) + b - 1 = K * (c : ℤ) + (b - 1) := by ring
    have e2 : K * ((c % d : ℕ) : ℤ) + b - 1 = K * ((c % d : ℕ) : ℤ) + (b - 1) := by ring
    rw [e1, e2]
    exact h
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨fun h => ha (h1.mpr h), fun h4 h43 h => hb h4 h43 (h2.mpr h)⟩
  · rintro ⟨ha, hb⟩
    exact ⟨fun h => ha (h1.mp h), fun h4 h43 h => hb h4 h43 (h2.mp h)⟩

/-- Counting over a product of coprime moduli: the CRT splits the filter over `insert p S'`
into a product of the filtered ranges. -/
private theorem card_insert_mul_concrete (K b : ℤ) {p : ℕ} {S' : Finset ℕ}
    (hpS' : p ∉ S') {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : x.Coprime y)
    (hpx : p ∣ x) (hyS : ∀ q ∈ S', q ∣ y) :
    #((Finset.range (x * y)).filter (fun c : ℕ => ∀ p₀ ∈ insert p S',
        (¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b ∧
          (p₀ % 4 = 3 → p₀ ≠ 3 → ¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b - 1))))
      = #((Finset.range x).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
          (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1)))
        * #((Finset.range y).filter (fun c : ℕ => ∀ p₀ ∈ S',
        (¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b ∧
          (p₀ % 4 = 3 → p₀ ≠ 3 → ¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b - 1)))) := by
  classical
  have hx0 : x ≠ 0 := by omega
  have hy0 : y ≠ 0 := by omega
  have hmain : #((Finset.range (x * y)).filter (fun c : ℕ => ∀ p₀ ∈ insert p S',
        (¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b ∧
          (p₀ % 4 = 3 → p₀ ≠ 3 → ¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b - 1))))
      = #(((Finset.range x).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
            (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1))) ×ˢ
          ((Finset.range y).filter (fun c : ℕ => ∀ p₀ ∈ S',
            (¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b ∧
              (p₀ % 4 = 3 → p₀ ≠ 3 → ¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b - 1))))) := by
    apply Finset.card_bij (fun c _ => (c % x, c % y))
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_range] at hc
      obtain ⟨hclt, hcond⟩ := hc
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨Nat.mod_lt c (by omega), ?_⟩, Nat.mod_lt c (by omega), fun q hq => ?_⟩
      · exact (cond_iff_cond_mod K b hpx).mp
          (hcond p (Finset.mem_insert_self p S'))
      · exact (cond_iff_cond_mod K b (hyS q hq)).mp
          (hcond q (Finset.mem_insert_of_mem hq))
    · intro c1 hc1 c2 hc2 heq
      simp only [Finset.mem_filter, Finset.mem_range] at hc1 hc2
      have e1 : c1 % x = c2 % x := congrArg Prod.fst heq
      have e2 : c1 % y = c2 % y := congrArg Prod.snd heq
      have hm : c1 ≡ c2 [MOD x * y] :=
        (Nat.modEq_and_modEq_iff_modEq_mul hxy).mp ⟨e1, e2⟩
      exact hm.eq_of_lt_of_lt hc1.1 hc2.1
    · intro v hv
      obtain ⟨u, v'⟩ := v
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hv
      obtain ⟨⟨hu, hcu⟩, hv', hcv⟩ := hv
      set a : ℕ := (Nat.chineseRemainder hxy u v').val with ha
      have ham : a % x = u := by
        have h2 : a % x = u % x := (Nat.chineseRemainder hxy u v').prop.1
        rw [Nat.mod_eq_of_lt hu] at h2
        exact h2
      have han : a % y = v' := by
        have h2 : a % y = v' % y := (Nat.chineseRemainder hxy u v').prop.2
        rw [Nat.mod_eq_of_lt hv'] at h2
        exact h2
      have halt : a < x * y := Nat.chineseRemainder_lt_mul hxy u v' hx0 hy0
      refine ⟨a, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨halt, fun q hq => ?_⟩
        rcases Finset.mem_insert.mp hq with hq' | hq'
        · subst hq'
          exact (cond_iff_cond_mod K b hpx).mpr
            (by rw [ham]; exact hcu)
        · exact (cond_iff_cond_mod K b (hyS q hq')).mpr
            (by rw [han]; exact hcv q hq')
      · show (a % x, a % y) = (u, v')
        rw [ham, han]
  rw [hmain, Finset.card_product]

/-- Counting modulo a prime power: the condition depends only on the residue modulo `p`, and
each residue modulo `p` occurs `p^(k-1)` times below `p^k`. -/
private theorem card_pow_concrete (K b : ℤ) {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    #((Finset.range (p ^ k)).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
        (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1)))
      = #((Finset.range p).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
          (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1))) * p ^ (k - 1) := by
  classical
  have hp0 : 0 < p := hp.pos
  have hpk : p ^ k = p * p ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [Nat.pow_succ']
  have hmain : #((Finset.range (p ^ k)).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
        (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1)))
      = #(((Finset.range p).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
          (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1))) ×ˢ
          (Finset.range (p ^ (k - 1)))) := by
    apply Finset.card_bij (fun c _ => (c % p, c / p))
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_range] at hc
      obtain ⟨hclt, hcP⟩ := hc
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨Nat.mod_lt c hp0, (cond_iff_cond_mod K b (dvd_refl p)).mp hcP⟩, ?_⟩
      rw [Nat.div_lt_iff_lt_mul hp0, Nat.mul_comm (p ^ (k - 1)) p, ← hpk]
      exact hclt
    · intro c1 hc1 c2 hc2 heq
      have e1 : c1 % p = c2 % p := congrArg Prod.fst heq
      have e2 : c1 / p = c2 / p := congrArg Prod.snd heq
      calc c1 = p * (c1 / p) + c1 % p := (Nat.div_add_mod c1 p).symm
        _ = p * (c2 / p) + c2 % p := by rw [e2, e1]
        _ = c2 := Nat.div_add_mod c2 p
    · intro v hv
      obtain ⟨a, j⟩ := v
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hv
      obtain ⟨⟨ha1, haP⟩, hj1⟩ := hv
      refine ⟨a + p * j, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, ?_⟩
        · rw [hpk]
          calc a + p * j < p * (1 + j) := by
                have h1 : a + p * j < p + p * j := by omega
                have h2 : p + p * j = p * (1 + j) := by ring
                rwa [h2] at h1
            _ ≤ p * p ^ (k - 1) := Nat.mul_le_mul_left p (by omega)
        · exact (cond_iff_cond_mod K b (dvd_refl p)).mpr
            (by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha1]; exact haP)
      · show ((a + p * j) % p, (a + p * j) / p) = (a, j)
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha1]
        rw [Nat.add_mul_div_left a j hp0, Nat.div_eq_of_lt ha1, Nat.zero_add]
  rw [hmain, Finset.card_product, Finset.card_range]

/-- Exactly one residue modulo the prime `p` solves `K c + b = 0`, when `p` does not divide
`K`. -/
private theorem card_linear_dvd_eq_one (K : ℤ) {p : ℕ} (hp : p.Prime)
    (hK : ¬ (p : ℤ) ∣ K) (b : ℤ) :
    #((Finset.range p).filter (fun c : ℕ => (p : ℤ) ∣ K * (c : ℤ) + b)) = 1 := by
  classical
  set A : Finset ℕ := (Finset.range p).filter (fun c : ℕ => (p : ℤ) ∣ K * (c : ℤ) + b) with hA
  have huniq : ∀ a ∈ A, ∀ a' ∈ A, a = a' := by
    intro a ha a' ha'
    rw [hA, Finset.mem_filter, Finset.mem_range] at ha ha'
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨ha1', ha2'⟩ := ha'
    have hd : (p : ℤ) ∣ K * ((a : ℤ) - (a' : ℤ)) := by
      have h := dvd_sub ha2 ha2'
      have e : K * (a : ℤ) + b - (K * (a' : ℤ) + b) = K * ((a : ℤ) - (a' : ℤ)) := by ring
      rwa [e] at h
    have hpint : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpint.dvd_mul.mp hd with h | h
    · exact absurd h hK
    · have hmod : a ≡ a' [MOD p] := by
        rw [Nat.modEq_iff_dvd]
        simpa using dvd_neg.mpr h
      exact hmod.eq_of_lt_of_lt ha1 ha1'
  have hne : A.Nonempty := by
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero p := ⟨hp.pos.ne'⟩
    have hK0 : ((K : ℤ) : ZMod p) ≠ 0 := by
      intro h
      exact hK ((ZMod.intCast_zmod_eq_zero_iff_dvd K p).mp h)
    set x : ZMod p := (-((b : ℤ) : ZMod p)) * ((K : ℤ) : ZMod p)⁻¹ with hx
    have hzero : ((K : ℤ) : ZMod p) * x = -((b : ℤ) : ZMod p) := by
      rw [hx]
      have hring : ((K : ℤ) : ZMod p) * (-((b : ℤ) : ZMod p) * ((K : ℤ) : ZMod p)⁻¹)
          = -((b : ℤ) : ZMod p) * (((K : ℤ) : ZMod p) * ((K : ℤ) : ZMod p)⁻¹) := by ring
      rw [hring, mul_inv_cancel₀ hK0, mul_one]
    have hxval : (((x.val : ℕ)) : ZMod p) = x := ZMod.natCast_zmod_val x
    refine ⟨x.val, ?_⟩
    rw [hA, Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt x, ?_⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hcast : (((K * ((x.val : ℕ) : ℤ) + b : ℤ)) : ZMod p)
        = ((K : ℤ) : ZMod p) * x + ((b : ℤ) : ZMod p) := by
      push_cast
      rw [hxval]
    rw [hcast, hzero]
    ring
  exact Nat.le_antisymm (Finset.card_le_one.mpr huniq)
    (Nat.succ_le_of_lt (Finset.card_pos.mpr hne))

/-- The number of residues modulo the prime `p ≠ 3` satisfying the two local conditions of
display (5.1) is `p - omega p` with `omega p = 2` for `p = 3 mod 4` and `1` otherwise. -/
private theorem card_residues_prime (K b : ℤ) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hK : ¬ (p : ℤ) ∣ K) :
    #((Finset.range p).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
        (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1)))
      = p - (if p % 4 = 3 then 2 else 1) := by
  classical
  set A0 : Finset ℕ := (Finset.range p).filter (fun c : ℕ => (p : ℤ) ∣ K * (c : ℤ) + b) with hA0
  set A1 : Finset ℕ :=
    (Finset.range p).filter (fun c : ℕ => (p : ℤ) ∣ K * (c : ℤ) + b - 1) with hA1
  have h0 : #A0 = 1 := card_linear_dvd_eq_one K hp hK b
  have h1 : #A1 = 1 := by
    rw [hA1]
    have hfil : (Finset.range p).filter (fun c : ℕ => (p : ℤ) ∣ K * (c : ℤ) + b - 1)
        = (Finset.range p).filter (fun c : ℕ => (p : ℤ) ∣ K * (c : ℤ) + (b - 1)) :=
      Finset.filter_congr (fun c _ => by
        have e : K * (c : ℤ) + b - 1 = K * (c : ℤ) + (b - 1) := by ring
        rw [e])
    rw [hfil]
    exact card_linear_dvd_eq_one K hp hK (b - 1)
  have hdisj : Disjoint A0 A1 := by
    rw [Finset.disjoint_left]
    intro c hc0 hc1
    rw [hA0, Finset.mem_filter] at hc0
    rw [hA1, Finset.mem_filter] at hc1
    have hd : (p : ℤ) ∣ 1 := by
      have h := dvd_sub hc0.2 hc1.2
      have e' : K * (c : ℤ) + b - (K * (c : ℤ) + b - 1) = 1 := by ring
      rwa [e'] at h
    have : p ∣ 1 := by exact_mod_cast hd
    exact hp.not_dvd_one this
  have hsubU : A0 ∪ A1 ⊆ Finset.range p := by
    intro c hc
    rcases Finset.mem_union.mp hc with h | h
    · rw [hA0, Finset.mem_filter] at h; exact h.1
    · rw [hA1, Finset.mem_filter] at h; exact h.1
  have hsub0 : A0 ⊆ Finset.range p := by
    intro c hc
    rw [hA0, Finset.mem_filter] at hc; exact hc.1
  by_cases h43 : p % 4 = 3
  · have hguard : ∀ c : ℕ, (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1)
        ↔ ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1 := by
      intro c
      exact ⟨fun h => h h43 hp3, fun h _ _ => h⟩
    have hT1 : (Finset.range p).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
        (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1))
        = (Finset.range p).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
          ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1) :=
      Finset.filter_congr (fun c _ => by rw [hguard c])
    have hT2 : (Finset.range p).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
        ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1) = Finset.range p \ (A0 ∪ A1) := by
      ext c
      rw [Finset.mem_filter, Finset.mem_sdiff, hA0, hA1, Finset.mem_union,
        Finset.mem_filter, Finset.mem_filter, not_or, not_and, not_and]
      constructor
      · rintro ⟨hlt, hP0, hP1⟩
        exact ⟨hlt, fun _ => hP0, fun _ => hP1⟩
      · rintro ⟨hlt, hQ0, hQ1⟩
        exact ⟨hlt, hQ0 hlt, hQ1 hlt⟩
    rw [hT1, hT2, if_pos h43, Finset.card_sdiff_of_subset hsubU,
      Finset.card_union_of_disjoint hdisj, h0, h1, Finset.card_range]
  · have hguard : ∀ c : ℕ, (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1) :=
      fun c h => absurd h h43
    have hT1 : (Finset.range p).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
        (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1))
        = (Finset.range p).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b) :=
      Finset.filter_congr (fun c _ => by
        constructor
        · rintro ⟨h, _⟩; exact h
        · intro h; exact ⟨h, hguard c⟩)
    have hT2 : (Finset.range p).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b)
        = Finset.range p \ A0 := by
      ext c
      rw [Finset.mem_filter, Finset.mem_sdiff, hA0, Finset.mem_filter, not_and]
      constructor
      · rintro ⟨hlt, hP0⟩
        exact ⟨hlt, fun _ => hP0⟩
      · rintro ⟨hlt, hQ0⟩
        exact ⟨hlt, hQ0 hlt⟩
    rw [hT1, hT2, if_neg h43, Finset.card_sdiff_of_subset hsub0, h0, Finset.card_range]

/-- The count of residues modulo `∏ x ∈ S, x^(e x)` satisfying the conditions of display (5.1)
at every prime of `S` is the product of the local counts. -/
private theorem card_prod_pow (K b : ℤ) (e : ℕ → ℕ) (S : Finset ℕ)
    (hSp : ∀ p ∈ S, p.Prime) (hS3 : ∀ p ∈ S, p ≠ 3)
    (hSe : ∀ p ∈ S, 1 ≤ e p) (hKS : ∀ p ∈ S, ¬ (p : ℤ) ∣ K) :
    #((Finset.range (∏ x ∈ S, x ^ e x)).filter (fun c : ℕ => ∀ p₀ ∈ S,
        (¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b ∧
          (p₀ % 4 = 3 → p₀ ≠ 3 → ¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b - 1))))
      = ∏ x ∈ S, (x ^ e x - (if x % 4 = 3 then 2 else 1) * x ^ (e x - 1)) := by
  classical
  revert hSp hS3 hSe hKS
  induction S using Finset.induction with
  | empty =>
      intro hSp hS3 hSe hKS
      rw [Finset.prod_empty]
      rw [show (Finset.range 1).filter (fun c : ℕ => ∀ p₀ ∈ (∅ : Finset ℕ),
          (¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b ∧
            (p₀ % 4 = 3 → p₀ ≠ 3 → ¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b - 1))) = Finset.range 1 from
        Finset.filter_true_of_mem (fun c _ => by simp)]
      rw [Finset.card_range, Finset.prod_empty]
  | insert p S' hpS' ih =>
      intro hSp hS3 hSe hKS
      have hpp : p.Prime := hSp p (Finset.mem_insert_self p S')
      have hSp' : ∀ q ∈ S', q.Prime := fun q hq => hSp q (Finset.mem_insert_of_mem hq)
      have hS3p : p ≠ 3 := hS3 p (Finset.mem_insert_self p S')
      have hS3' : ∀ q ∈ S', q ≠ 3 := fun q hq => hS3 q (Finset.mem_insert_of_mem hq)
      have hSep : 1 ≤ e p := hSe p (Finset.mem_insert_self p S')
      have hSep0 : e p ≠ 0 := by omega
      have hSe' : ∀ q ∈ S', 1 ≤ e q := fun q hq => hSe q (Finset.mem_insert_of_mem hq)
      have hKp : ¬ (p : ℤ) ∣ K := hKS p (Finset.mem_insert_self p S')
      have hK' : ∀ q ∈ S', ¬ (q : ℤ) ∣ K := fun q hq => hKS q (Finset.mem_insert_of_mem hq)
      have hcop : (p ^ e p).Coprime (∏ x ∈ S', x ^ e x) := by
        rw [Nat.coprime_prod_right_iff]
        intro q hq
        have hpq : p ≠ q := fun h => hpS' (h ▸ hq)
        exact (((Nat.coprime_primes hpp (hSp' q hq)).mpr hpq).pow_left (e p)).pow_right (e q)
      have hx1 : 1 ≤ p ^ e p := Nat.succ_le_of_lt (pow_pos hpp.pos _)
      have hy1 : 1 ≤ ∏ x ∈ S', x ^ e x :=
        Nat.succ_le_of_lt (Finset.prod_pos (fun q hq => pow_pos (hSp' q hq).pos _))
      have hpx : p ∣ p ^ e p := dvd_pow_self p hSep0
      have hyS : ∀ q ∈ S', q ∣ ∏ x ∈ S', x ^ e x := by
        intro q hq
        have hq0 : e q ≠ 0 := by have := hSe' q hq; omega
        exact (dvd_pow_self q hq0).trans (Finset.dvd_prod_of_mem (fun x => x ^ e x) hq)
      rw [Finset.prod_insert hpS', Finset.prod_insert hpS']
      refine (card_insert_mul_concrete K b hpS' hx1 hy1 hcop hpx hyS).trans ?_
      rw [card_pow_concrete K b hpp hSep, card_residues_prime K b hpp hS3p hKp]
      have hS'val : #((Finset.range (∏ x ∈ S', x ^ e x)).filter (fun c : ℕ => ∀ p₀ ∈ S',
          (¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b ∧
            (p₀ % 4 = 3 → p₀ ≠ 3 → ¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b - 1))))
          = ∏ x ∈ S', (x ^ e x - (if x % 4 = 3 then 2 else 1) * x ^ (e x - 1)) :=
        ih hSp' hS3' hSe' hK'
      rw [hS'val]
      have harith : p ^ e p - (if p % 4 = 3 then 2 else 1) * p ^ (e p - 1)
          = (p - (if p % 4 = 3 then 2 else 1)) * p ^ (e p - 1) := by
        have hpk : p ^ e p = p * p ^ (e p - 1) := by
          conv_lhs => rw [show e p = (e p - 1) + 1 by omega]
          rw [Nat.pow_succ']
        rw [hpk, Nat.sub_mul]
      rw [harith]

/-- The same count for a modulus given as the product, needed to read off the count at `q`. -/
private theorem card_count_of_eq_prod (K b : ℤ) (N : ℕ) (S : Finset ℕ) (e : ℕ → ℕ)
    (hN : N = ∏ x ∈ S, x ^ e x) (hSp : ∀ p ∈ S, p.Prime) (hS3 : ∀ p ∈ S, p ≠ 3)
    (hSe : ∀ p ∈ S, 1 ≤ e p) (hKS : ∀ p ∈ S, ¬ (p : ℤ) ∣ K) :
    #((Finset.range N).filter (fun c : ℕ => ∀ p₀ ∈ S,
        (¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b ∧
          (p₀ % 4 = 3 → p₀ ≠ 3 → ¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b - 1))))
      = ∏ x ∈ S, (x ^ e x - (if x % 4 = 3 then 2 else 1) * x ^ (e x - 1)) := by
  subst hN
  exact card_prod_pow K b e S hSp hS3 hSe hKS

private theorem leaf_qres_count (J w : ℕ) (hJ : 5 ≤ J) (hw : wBig ≤ w) (b : ℤ)
    (hb : Amenable (WW J w) b) (q Q' : ℕ) (hq : 1 ≤ q) (hQ' : Q'.Coprime q)
    (hqW : IsCoprime (q : ℤ) (WW J w)) :
    (#(QRes q (WW J w * Q') b) : ℝ) =
      q * ∏ p ∈ q.primeFactors, (1 - (if p % 4 = 3 then (2 : ℝ) else 1) / p) := by
  classical
  have hq0 : q ≠ 0 := by omega
  have h3W : (3 : ℤ) ∣ WW J w := by
    show (3 : ℤ) ∣ Wmod J (Sw w)
    exact (by norm_num : (3 : ℤ) ∣ 27).trans (dvd27_Wmod J (Sw w))
  have hne3 : ∀ p ∈ q.primeFactors, p ≠ 3 := by
    intro p hp hp3
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpq : (p : ℤ) ∣ (q : ℤ) := by exact_mod_cast Nat.dvd_of_mem_primeFactors hp
    have hpW : (p : ℤ) ∣ WW J w := by rw [hp3]; exact h3W
    have hg : (p : ℤ) ∣ ((Int.gcd (q : ℤ) (WW J w) : ℕ) : ℤ) := by
      exact_mod_cast Int.dvd_gcd hpq hpW
    rw [Int.isCoprime_iff_gcd_eq_one.mp hqW] at hg
    have h1 : (p : ℤ) ∣ (1 : ℤ) := by simpa using hg
    exact hpp.not_dvd_one (by exact_mod_cast h1)
  have hfac1 : ∀ p ∈ q.primeFactors, 1 ≤ q.factorization p := by
    intro p hp
    exact Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hq0
      (Nat.dvd_of_mem_primeFactors hp)
  have hKW : ∀ p ∈ q.primeFactors, ¬ (p : ℤ) ∣ WW J w * (Q' : ℤ) := by
    intro p hp hdvd
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpq : (p : ℤ) ∣ (q : ℤ) := by exact_mod_cast Nat.dvd_of_mem_primeFactors hp
    rcases (Nat.prime_iff_prime_int.mp hpp).dvd_mul.mp hdvd with h | h
    · have hg : (p : ℤ) ∣ ((Int.gcd (q : ℤ) (WW J w) : ℕ) : ℤ) := by
        exact_mod_cast Int.dvd_gcd hpq h
      rw [Int.isCoprime_iff_gcd_eq_one.mp hqW] at hg
      have h1 : (p : ℤ) ∣ (1 : ℤ) := by simpa using hg
      exact hpp.not_dvd_one (by exact_mod_cast h1)
    · have hpq' : p ∣ Q' := by exact_mod_cast h
      have h1 : p ∣ Nat.gcd Q' q := Nat.dvd_gcd hpq' (Nat.dvd_of_mem_primeFactors hp)
      rw [hQ'] at h1
      exact hpp.not_dvd_one h1
  have hN : q = ∏ p ∈ q.primeFactors, p ^ q.factorization p :=
    Nat.prod_primeFactors_pow_factorization hq0
  have hcount := card_count_of_eq_prod (WW J w * (Q' : ℤ)) b q q.primeFactors
    (fun p => q.factorization p) hN (fun p hp => Nat.prime_of_mem_primeFactors hp) hne3 hfac1 hKW
  have hcop_iff : ∀ c : ℕ, (IsCoprime (WW J w * (Q' : ℤ) * (c : ℤ) + b) (q : ℤ) ↔
      ∀ p ∈ q.primeFactors, ¬ (p : ℤ) ∣ WW J w * (Q' : ℤ) * (c : ℤ) + b) := by
    intro c
    constructor
    · intro hc p hp hdvd
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpq : (p : ℤ) ∣ (q : ℤ) := by exact_mod_cast Nat.dvd_of_mem_primeFactors hp
      have hg : (p : ℤ) ∣
          ((Int.gcd (WW J w * (Q' : ℤ) * (c : ℤ) + b) (q : ℤ) : ℕ) : ℤ) := by
        exact_mod_cast Int.dvd_gcd hdvd hpq
      rw [Int.isCoprime_iff_gcd_eq_one.mp hc] at hg
      have h1 : (p : ℤ) ∣ (1 : ℤ) := by simpa using hg
      exact hpp.not_dvd_one (by exact_mod_cast h1)
    · intro h
      rw [Int.isCoprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd hne
      have h2 := Int.dvd_gcd_iff.mp hpd
      have hmem : p ∈ q.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpp, by exact_mod_cast h2.2, hq0⟩
      exact h p hmem h2.1
  have hQRes : QRes q (WW J w * (Q' : ℤ)) b = (Finset.range q).filter (fun c : ℕ =>
      ∀ p₀ ∈ q.primeFactors,
        (¬ (p₀ : ℤ) ∣ WW J w * (Q' : ℤ) * (c : ℤ) + b ∧
          (p₀ % 4 = 3 → p₀ ≠ 3 → ¬ (p₀ : ℤ) ∣ WW J w * (Q' : ℤ) * (c : ℤ) + b - 1))) := by
    ext c
    simp only [QRes, mem_filter, mem_range]
    constructor
    · rintro ⟨hlt, hcop, hcond⟩
      refine ⟨hlt, fun p hp => ⟨(hcop_iff c).mp hcop p hp, ?_⟩⟩
      intro h4 h43 hdvd
      exact hcond p (Nat.prime_of_mem_primeFactors hp) h4 h43
        (Nat.dvd_of_mem_primeFactors hp) hdvd
    · rintro ⟨hlt, hcond⟩
      refine ⟨hlt, (hcop_iff c).mpr (fun p hp => (hcond p hp).1), ?_⟩
      intro p hpp h4 h43 hpq hdvd
      exact (hcond p (Nat.mem_primeFactors.mpr ⟨hpp, hpq, hq0⟩)).2 h4 h43 hdvd
  have hfac : ∀ x ∈ q.primeFactors,
      ((x ^ q.factorization x - (if x % 4 = 3 then 2 else 1) * x ^ (q.factorization x - 1) :
          ℕ) : ℝ)
        = ((x : ℝ) ^ q.factorization x) *
            (1 - (if x % 4 = 3 then (2 : ℝ) else 1) / (x : ℝ)) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hk1 : 1 ≤ q.factorization p := hfac1 p hp
    set c : ℕ := if p % 4 = 3 then 2 else 1 with hc
    have hcle : c * p ^ (q.factorization p - 1) ≤ p ^ q.factorization p := by
      have hpk : p ^ q.factorization p = p * p ^ (q.factorization p - 1) := by
        conv_lhs => rw [show q.factorization p = (q.factorization p - 1) + 1 by omega]
        rw [Nat.pow_succ']
      rw [hpk]
      have hc2 : c ≤ 2 := by
        rw [hc]; split_ifs <;> norm_num
      calc c * p ^ (q.factorization p - 1) ≤ 2 * p ^ (q.factorization p - 1) :=
            Nat.mul_le_mul_right _ hc2
        _ ≤ p * p ^ (q.factorization p - 1) := Nat.mul_le_mul_right _ hpp.two_le
    rw [Nat.cast_sub hcle, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
    have hccast : ((c : ℕ) : ℝ) = (if p % 4 = 3 then (2 : ℝ) else 1) := by
      rw [hc]; split_ifs <;> norm_num
    rw [hccast]
    have hp0 : (p : ℝ) ≠ 0 := by
      have hpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
      linarith
    have hpk : (p : ℝ) ^ q.factorization p
        = (p : ℝ) * (p : ℝ) ^ (q.factorization p - 1) := by
      conv_lhs => rw [show q.factorization p = (q.factorization p - 1) + 1 by omega]
      rw [pow_succ']
    have hWp : ((p : ℝ) * (p : ℝ) ^ (q.factorization p - 1)) *
        ((if p % 4 = 3 then (2 : ℝ) else 1) / (p : ℝ))
        = (if p % 4 = 3 then (2 : ℝ) else 1) * (p : ℝ) ^ (q.factorization p - 1) := by
      rw [mul_div_assoc']
      have hr : ((p : ℝ) * (p : ℝ) ^ (q.factorization p - 1)) *
          (if p % 4 = 3 then (2 : ℝ) else 1)
          = (p : ℝ) * ((if p % 4 = 3 then (2 : ℝ) else 1) *
              (p : ℝ) ^ (q.factorization p - 1)) := by ring
      rw [hr]
      exact mul_div_cancel_left₀ _ hp0
    rw [hpk, mul_sub, mul_one, hWp]
  have hcard : #(QRes q (WW J w * (Q' : ℤ)) b)
      = ∏ x ∈ q.primeFactors,
          (x ^ q.factorization x - (if x % 4 = 3 then 2 else 1) * x ^ (q.factorization x - 1)) := by
    rw [hQRes]
    exact hcount
  rw [hcard, Nat.cast_prod]
  trans ∏ x ∈ q.primeFactors,
      (((x : ℝ) ^ q.factorization x) * (1 - (if x % 4 = 3 then (2 : ℝ) else 1) / (x : ℝ)))
  · exact Finset.prod_congr rfl (fun p hp => hfac p hp)
  · rw [Finset.prod_mul_distrib]
    have hcast : ((∏ x ∈ q.primeFactors, x ^ q.factorization x : ℕ) : ℝ)
        = ∏ x ∈ q.primeFactors, ((x : ℝ) ^ q.factorization x) := by
      rw [Nat.cast_prod]
      simp
    have hqprod : (∏ x ∈ q.primeFactors, ((x : ℝ) ^ q.factorization x)) = (q : ℝ) := by
      rw [← hcast]
      exact congrArg (fun n : ℕ => (n : ℝ)) hN.symm
    rw [hqprod]

/-- wBig is at least 1024. -/
private theorem wBig_ge_1024 : (1024 : ℝ) ≤ wBig := by
  unfold wBig
  have h : (10 : ℝ) ^ ((4 : ℝ)) ≤ (10 : ℝ) ^ ((10 : ℝ) ^ (10 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (10 : ℝ) ^ (1 : ℝ) ≤ (10 : ℝ) ^ (10 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    simp at this
    linarith
  have h2 : (10 : ℝ) ^ ((4 : ℝ)) = 10000 := by norm_num
  linarith

/-- LEAF: proof of Lemma 5.3, page 21, the local density, the step
`q' q^{0.1} Q' ∏_{p ∣ Q', p > w} (1 - ω(p)/p) ≤ q' q^{0.2} ∏_{p ∣ q, p > w} (1 - ω(p)/p) · …`
read at the modulus `q`: by the count behind (5.2), `#{c₂ (mod q)} = q ∏_{p ∣ q} (1 - ω(p)/p)`
with `ω(p) ∈ {1, 2}`, and for `(q, W) = 1` every `p ∣ q` exceeds `w ≥ 10^{10^{10}}`, so the
product is at least `q^{-0.1}`. Class MEDIUM. -/
theorem local_density (J w : ℕ) (hJ : 5 ≤ J) (hw : wBig ≤ w) (b : ℤ)
    (hb : Amenable (WW J w) b) (q Q' : ℕ) (hq : 1 ≤ q) (hQ' : Q'.Coprime q)
    (hqW : IsCoprime (q : ℤ) (WW J w)) :
    (q : ℝ) ^ ((9 : ℝ) / 10) ≤ #(QRes q (WW J w * Q') b) := by
  rw [leaf_qres_count J w hJ hw b hb q Q' hq hQ' hqW]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hw1024 : (1024 : ℝ) ≤ w := wBig_ge_1024.trans hw
  have hfac : ∀ p ∈ q.primeFactors,
      (p : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1 - (if p % 4 = 3 then (2 : ℝ) else 1) / p := by
    intro p hp
    have hpw : w < p := prime_factor_gt_w hJ hqW hp
    have hp1024 : (1024 : ℝ) ≤ p := hw1024.trans (by exact_mod_cast hpw.le)
    have hp0 : (0 : ℝ) < p := by linarith
    have h2 : (2 : ℝ) ≤ (p : ℝ) ^ (1 / 10 : ℝ) := by
      calc (2 : ℝ) = (1024 : ℝ) ^ (1 / 10 : ℝ) := by
            rw [show (1024 : ℝ) = 2 ^ (10 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
            norm_num
        _ ≤ (p : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_le_rpow (by norm_num) hp1024 (by norm_num)
    have hneg : (p : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1 / 2 := by
      rw [Real.rpow_neg hp0.le]
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      linarith
    have hω : (if p % 4 = 3 then (2 : ℝ) else 1) / p ≤ 1 / 2 := by
      rw [div_le_iff₀ hp0]
      split_ifs <;> linarith
    linarith
  have hprod : ∏ p ∈ q.primeFactors, (p : ℝ) ^ (-(1 / 10 : ℝ)) ≤
      ∏ p ∈ q.primeFactors, (1 - (if p % 4 = 3 then (2 : ℝ) else 1) / p) :=
    prod_le_prod₀ (fun p _ => by positivity) hfac
  have hpf : ∏ p ∈ q.primeFactors, (p : ℝ) ^ (-(1 / 10 : ℝ)) =
      ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ (-(1 / 10 : ℝ)) := by
    push_cast
    rw [Real.finset_prod_rpow _ _ (fun p _ => by positivity)]
  have hle : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
  have hpos : (0 : ℝ) < ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (prod_ne_zero_iff.mpr fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hmono : (q : ℝ) ^ (-(1 / 10 : ℝ)) ≤
      ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ (-(1 / 10 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)
  have hq910 : (q : ℝ) ^ ((9 : ℝ) / 10) = q * (q : ℝ) ^ (-(1 / 10 : ℝ)) := by
    rw [← Real.rpow_one_add' hq0.le (by norm_num)]
    norm_num
  rw [hq910]
  apply mul_le_mul_of_nonneg_left _ hq0.le
  rw [hpf] at hprod
  exact hmono.trans hprod

/-- `wBig ≥ 100`. -/
theorem wBig_ge_100 : (100 : ℝ) ≤ wBig := by
  unfold wBig
  have h : (10 : ℝ) ^ ((2 : ℝ)) ≤ (10 : ℝ) ^ ((10 : ℝ) ^ (10 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (10 : ℝ) ^ (1 : ℝ) ≤ (10 : ℝ) ^ (10 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    simp at this
    linarith
  have h2 : (10 : ℝ) ^ ((2 : ℝ)) = 100 := by norm_num
  linarith

/-- A modulus `q ≠ 1` coprime to `W` exceeds `w`, as all its primes do. -/
theorem w_lt_of_coprime {J w q : ℕ} (hJ : 5 ≤ J) (hq1 : q ≠ 1) (hq0 : q ≠ 0)
    (hqW : IsCoprime (q : ℤ) (WW J w)) : w < q := by
  obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd hq1
  have hmem : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpq, hq0⟩
  have := prime_factor_gt_w hJ hqW hmem
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hpq
  omega

/-- **Lemma 5.3**, page 19, display (5.4), from the leaves above and the divisor bound
`τ(q) ≤ q^{1/5}` of `RoughDivisors`, following pages 20 to 21. -/
theorem lemma53_of_leaves : Lemma53 := by
  intro J w hJ hw b hb Q q a hQ hqQ hq1 ha haq
  by_cases hqW : IsCoprime (q : ℤ) (WW J w)
  swap
  · rw [sum_eq_zero_of_not_coprime J w b Q q a hQ hqQ haq hqW, norm_zero]
    apply mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hqQ
    omega
  have hw100 : (100 : ℝ) ≤ w := wBig_ge_100.trans hw
  have hw32 : 32 ≤ w := by
    have : (32 : ℝ) ≤ w := by linarith
    exact_mod_cast this
  obtain ⟨q', Q', -, hQ'q, -, hmain⟩ :=
    sum_bound_of_coprime J w hJ hw b hb Q q a hQ hqQ hq1 ha haq hqW
  have hdens := local_density J w hJ hw b hb q Q' (Nat.pos_of_ne_zero hq0) hQ'q hqW
  have htau := divisor_card_le_fifth_of_coprime_WW hJ hw32 hq0 hqW
  have hwq : w < q := w_lt_of_coprime hJ hq1 hq0 hqW
  set S := ‖∑ c₀ ∈ QRes Q (WW J w) b, eC ((a : ℝ) * c₀ / q)‖
  set K : ℝ := (#(QRes Q (WW J w) b) : ℝ)
  set A : ℝ := (#(QRes q (WW J w * Q') b) : ℝ)
  have hS : 0 ≤ S := norm_nonneg _
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hwpos : (0 : ℝ) < w := by linarith
  have hqw : (w : ℝ) ≤ q := by exact_mod_cast hwq.le
  -- `S q^{9/10} ≤ S A ≤ τ(q) K ≤ q^{1/5} K`
  have h1 : S * (q : ℝ) ^ ((9 : ℝ) / 10) ≤ (q : ℝ) ^ ((1 : ℝ) / 5) * K := by
    calc S * (q : ℝ) ^ ((9 : ℝ) / 10) ≤ S * A := mul_le_mul_of_nonneg_left hdens hS
      _ ≤ (q.divisors.card : ℝ) * K := hmain
      _ ≤ (q : ℝ) ^ ((1 : ℝ) / 5) * K := mul_le_mul_of_nonneg_right htau hK
  have hpos9 : 0 < (q : ℝ) ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos hqpos _
  have hsplit : (q : ℝ) ^ ((1 : ℝ) / 5) = (q : ℝ) ^ (-(7 : ℝ) / 10) * (q : ℝ) ^ ((9 : ℝ) / 10) := by
    rw [← Real.rpow_add hqpos]; norm_num
  have h2 : S ≤ (q : ℝ) ^ (-(7 : ℝ) / 10) * K := by
    rw [hsplit] at h1
    have : S * (q : ℝ) ^ ((9 : ℝ) / 10) ≤ ((q : ℝ) ^ (-(7 : ℝ) / 10) * K) * (q : ℝ) ^ ((9 : ℝ) / 10) := by
      linarith [h1]
    exact le_of_mul_le_mul_right this hpos9
  have h3 : (q : ℝ) ^ (-(7 : ℝ) / 10) ≤ (w : ℝ) ^ (-(1 : ℝ) / 2) := by
    calc (q : ℝ) ^ (-(7 : ℝ) / 10) ≤ (w : ℝ) ^ (-(7 : ℝ) / 10) :=
          Real.rpow_le_rpow_of_nonpos hwpos hqw (by norm_num)
      _ ≤ (w : ℝ) ^ (-(1 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  calc S ≤ (q : ℝ) ^ (-(7 : ℝ) / 10) * K := h2
    _ ≤ (w : ℝ) ^ (-(1 : ℝ) / 2) * K := mul_le_mul_of_nonneg_right h3 hK

end LeanLab.Teravainen2016.Lemma53Split

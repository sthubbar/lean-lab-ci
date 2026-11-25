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
  sorry

/-- LEAF: proof of Lemma 5.3, page 21, the local density, the step
`q' q^{0.1} Q' ∏_{p ∣ Q', p > w} (1 - ω(p)/p) ≤ q' q^{0.2} ∏_{p ∣ q, p > w} (1 - ω(p)/p) · …`
read at the modulus `q`: by the count behind (5.2), `#{c₂ (mod q)} = q ∏_{p ∣ q} (1 - ω(p)/p)`
with `ω(p) ∈ {1, 2}`, and for `(q, W) = 1` every `p ∣ q` exceeds `w ≥ 10^{10^{10}}`, so the
product is at least `q^{-0.1}`. Class MEDIUM. -/
theorem local_density (J w : ℕ) (hJ : 5 ≤ J) (hw : wBig ≤ w) (b : ℤ)
    (hb : Amenable (WW J w) b) (q Q' : ℕ) (hq : 1 ≤ q) (hQ' : Q'.Coprime q)
    (hqW : IsCoprime (q : ℤ) (WW J w)) :
    (q : ℝ) ^ ((9 : ℝ) / 10) ≤ #(QRes q (WW J w * Q') b) := by
  sorry

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

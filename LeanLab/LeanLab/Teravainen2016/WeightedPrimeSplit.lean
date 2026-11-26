/-
P0076 J. Teräväinen, arXiv 1611.08585, Section 5, pages 17 to 21: Proposition 3.2 and its
half interval variant from Proposition 5.1 together with Lemmas 5.2 and 5.3, by splitting the
sum over `n` into residue classes `c₀ (mod Q)`, `c₀ ∈ 𝒬`.
AI wrote this Lean code, Claude, session CLOUD-S62. Checked only by the Lean kernel.
The binary Goldbach conjecture is OPEN.
-/
import LeanLab.Teravainen2016.MainInputs
import LeanLab.Teravainen2016.SieveResidues

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- The set `𝒬` of display (5.1), page 18, as residues `0 ≤ c₀ < Q`:
`(W c₀ + b, Q) = (W c₀ + b - 1, s(Q)) = 1`, the second condition read prime by prime as in
`Amenable`, `s(Q)` being the product of the primes `p ∣ Q`, `p ≡ -1 (mod 4)`, `p ≠ 3`. -/
noncomputable def QRes (Q : ℕ) (W b : ℤ) : Finset ℕ :=
  (range Q).filter (fun c₀ => IsCoprime (W * c₀ + b) (Q : ℤ) ∧
    ∀ p : ℕ, p.Prime → p % 4 = 3 → p ≠ 3 → p ∣ Q → ¬ (p : ℤ) ∣ W * c₀ + b - 1)

/-- **Proposition 5.1**, page 18, on the summation range `R N`. For the dyadic range the paper's
`n ∼ N` is `n ∼ N/3` here, the rescaling of (5.3); `|t| ≤ 5 (N/3)`; the factor
`δ₁ (log N)^{-3/2} (W/φ(W))^{3/2}` is moved to the left as the weight of `fW`; the term
`o(N/Q)` inside the bracket is `- ε N / Q` for every `ε > 0` once `N ≥ N₀(w, C, ε)`, uniformly in
`χ`, `b`, `t`, `c₀`. `Q ≤ (log N)^B` depends only on `χ` and `N`, and `B ≪_C 1`. The shift is
restricted to `0 ≤ b < W` as in `Prop32On`. -/
def Prop51On (R : ℕ → Finset ℕ) : Prop :=
  ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ Cc : ℕ, ∃ B : ℕ, ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → (Cc : ℝ) ^ 20 ≤ w →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ χ : ℤ → ℝ, (∀ n, 0 ≤ χ n) → FourierComplexityLE χ Cc →
    ∀ N : ℕ, N₀ ≤ N → ∃ Q : ℕ, 1 ≤ Q ∧ (Q : ℝ) ≤ Real.log N ^ B ∧
    ∀ b : ℤ, 0 ≤ b → b < WW J w → Amenable (WW J w) b →
    ∀ t : ℤ, |(t : ℝ)| ≤ 5 * (N : ℝ) / 3 → ∀ c₀ ∈ QRes Q (WW J w) b,
      δ₁ * ((Q : ℝ) / #(QRes Q (WW J w) b)) *
          (∑ n ∈ (R N).filter (fun n => n % Q = c₀), χ (t - n) - ε * N / Q) ≤
        Real.log N ^ ((3 : ℝ) / 2) * ((Nat.totient (WW J w).toNat : ℝ) / WW J w) ^ ((3 : ℝ) / 2) *
          ∑ n ∈ ((R N).filter (fun n : ℕ => Good (WW J w * (n : ℤ) + b))).filter
            (fun n => n % Q = c₀),
            χ (t - n)

/-- **Lemma 5.2**, page 18, quoting Matomäki and Shao Lemma 7.4, on the summation range `R N`:
the scale `n ∼ N` of the paper is `R N` here, so `N ≥ 2 Q²` becomes `6 Q² ≤ N` and the error
is stated with the larger `N`. The premise on `𝒬` is read for positive `a`, which loses nothing
since `e(a c₀/q)` depends on `a mod q`. `𝒬` is nonempty, as `Q/|𝒬|` requires. -/
def Lemma52On (R : ℕ → Finset ℕ) : Prop :=
  ∃ C' : ℝ, 0 < C' ∧ ∀ (Cc : ℕ) (χ : ℤ → ℝ), (∀ n, 0 ≤ χ n) → FourierComplexityLE χ Cc →
    ∀ N Q : ℕ, 1 ≤ Q → 6 * Q ^ 2 ≤ N → ∀ 𝒬 : Finset ℕ, 𝒬 ⊆ range Q → 𝒬.Nonempty →
    ∀ η₀ : ℝ, 0 < η₀ → (∀ q a : ℕ, q ∣ Q → q ≠ 1 → 0 < a → a.Coprime q →
        ‖∑ c₀ ∈ 𝒬, eC ((a : ℝ) * c₀ / q)‖ ≤ η₀ * #𝒬) →
    ∀ t : ℤ, (∑ n ∈ R N, χ (t - n)) - C' * (η₀ * (Cc : ℝ) ^ 2 * N + Q * (Cc : ℝ) ^ 2 * Real.sqrt N) ≤
      (Q : ℝ) / #𝒬 * ∑ c₀ ∈ 𝒬, ∑ n ∈ (R N).filter (fun n => n % Q = c₀), χ (t - n)

/-- **Lemma 5.3**, page 19, display (5.4), for `𝒬` of (5.1) with `W`, `w` as in (3.3). -/
def Lemma53 : Prop :=
  ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ, Amenable (WW J w) b →
    ∀ Q q a : ℕ, 1 ≤ Q → q ∣ Q → q ≠ 1 → 0 < a → a.Coprime q →
      ‖∑ c₀ ∈ QRes Q (WW J w) b, eC ((a : ℝ) * c₀ / q)‖ ≤
        (w : ℝ) ^ (-(1 : ℝ) / 2) * #(QRes Q (WW J w) b)

/-- `𝒬 ≠ ∅`, the positivity of the product (5.2), page 18. -/
def QResNonempty : Prop :=
  ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ, Amenable (WW J w) b →
    ∀ Q : ℕ, 1 ≤ Q → (QRes Q (WW J w) b).Nonempty


/-! ### Port of the printed proof of Lemma 5.3 (pages 20 to 21)

The divisor bound for integers with large prime factors, as in `RoughDivisors`.
-/
namespace Lemma53Port


/-- A prime factor at least 32 pays for the fifth power of its divisor count. -/
theorem prime_power_divisor_factor_le {p : ℕ} (hp : 32 ≤ p) (k : ℕ) :
    (k + 1) ^ 5 ≤ p ^ k := by
  calc
    _ ≤ (2 ^ k) ^ 5 := Nat.pow_le_pow_left (Nat.succ_le_of_lt k.lt_two_pow_self) 5
    _ = (32 : ℕ) ^ k := by rw [← pow_mul, Nat.mul_comm k 5, pow_mul]; norm_num
    _ ≤ _ := Nat.pow_le_pow_left hp k

/-- If every prime factor of q is at least 32, tau q to the fifth is at most q. -/
theorem rough_divisor_card_pow_five {q : ℕ} (hq : q ≠ 0)
    (hrough : ∀ p ∈ q.primeFactors, 32 ≤ p) : q.divisors.card ^ 5 ≤ q := by
  rw [Nat.card_divisors hq, ← prod_pow]
  calc
    _ ≤ ∏ p ∈ q.primeFactors, p ^ q.factorization p :=
      prod_le_prod (fun p hp => prime_power_divisor_factor_le (hrough p hp) _)
    _ = q := (Nat.prod_primeFactors_pow_factorization hq).symm

/-- The real fifth power divisor bound used on page 21. -/
theorem rough_divisor_card_le_fifth {q : ℕ} (hq : q ≠ 0)
    (hrough : ∀ p ∈ q.primeFactors, 32 ≤ p) :
    (q.divisors.card : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) / 5) := by
  have hnat := rough_divisor_card_pow_five hq hrough
  have hr : ((q.divisors.card : ℝ) ^ (5 : ℕ)) ≤ (q : ℝ) := by exact_mod_cast hnat
  have hh := Real.rpow_le_rpow (by positivity) hr (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have he : ((q.divisors.card : ℝ) ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) = q.divisors.card := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rwa [he] at hh

/-- Coprimality with W excludes every prime factor at most w. -/
theorem prime_factor_gt_w {J w q p : ℕ} (hJ : 5 ≤ J)
    (hcop : IsCoprime (q : ℤ) (WW J w)) (hp : p ∈ q.primeFactors) : w < p := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpdq : (p : ℤ) ∣ (q : ℤ) := by exact_mod_cast Nat.dvd_of_mem_primeFactors hp
  by_contra hwp
  have hpw : p ≤ w := by omega
  have hpdW : (p : ℤ) ∣ WW J w := by
    by_cases hp2 : p = 2
    · subst p
      simpa [WW] using two_pow_dvd_Wmod (J := J) (k := 1) (Sw w) (by omega)
    by_cases hp3 : p = 3
    · subst p
      exact (by norm_num : (3 : ℤ) ∣ 27).trans (dvd27_Wmod J (Sw w))
    have hp5 : 5 ≤ p := by
      by_contra h
      have hp4 : p ≤ 4 := by omega
      interval_cases p <;> norm_num at hprime <;> omega
    exact dvd_Wmod_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp5, hpw⟩, hprime⟩)
  have hd := Int.dvd_gcd hpdq hpdW
  rw [Int.isCoprime_iff_gcd_eq_one.mp hcop] at hd
  have hone : p ∣ 1 := by exact_mod_cast hd
  exact hprime.not_dvd_one hone

/-- A direct elementary consequence for the modulus in display 3.3. -/
theorem divisor_card_le_fifth_of_coprime_WW {J w q : ℕ} (hJ : 5 ≤ J) (hw : 32 ≤ w)
    (hq : q ≠ 0) (hcop : IsCoprime (q : ℤ) (WW J w)) :
    (q.divisors.card : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) / 5) := by
  apply rough_divisor_card_le_fifth hq
  intro p hp
  have hh := prime_factor_gt_w hJ hcop hp
  omega





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


end Lemma53Port


/-! ### Port of the printed proof of Lemma 5.2 (page 18)

Matomaki and Shao Lemma 7.4, as proved in `Teravainen2016/Lemma52Split1122b.lean`.
-/
namespace Lemma52Port

/-! ### The character `eC` -/

private theorem eC_add1122b (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

private theorem eC_norm1122b (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  rw [Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by simp
  rw [h, Real.exp_zero]

private theorem eC_conj1122b (x : ℝ) : (starRingEnd ℂ) (eC x) = eC (-x) := by
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem eC_nat_mul1122b (k : ℕ) (x : ℝ) : eC ((k : ℝ) * x) = (eC x) ^ k := by
  unfold eC; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

private theorem eC_int1122b (m : ℤ) : eC (m : ℝ) = 1 := by
  unfold eC
  rw [Complex.exp_eq_one_iff]
  exact ⟨m, by push_cast; ring⟩

private theorem eC_eq_one_iff1122b (x : ℝ) : eC x = 1 ↔ ∃ m : ℤ, x = m := by
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

/-! ### Orthogonality of additive characters modulo `Q` -/

/-- `∑_{a mod Q} e(a m / Q) = Q 1_{Q ∣ m}`. -/
theorem orth1122b (Q : ℕ) (hQ : 1 ≤ Q) (m : ℤ) :
    ∑ a ∈ range Q, eC ((a : ℝ) * m / Q) = if (Q : ℤ) ∣ m then (Q : ℂ) else 0 := by
  have hQ' : (Q : ℝ) ≠ 0 := by
    have : (0 : ℝ) < Q := by exact_mod_cast hQ
    exact this.ne'
  have hterm : ∀ a : ℕ, eC ((a : ℝ) * m / Q) = eC ((m : ℝ) / Q) ^ a := by
    intro a; rw [← eC_nat_mul1122b]; congr 1; ring
  simp_rw [hterm]
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    have : eC ((Q : ℝ) * (j : ℝ) / Q) = 1 := by
      rw [show (Q : ℝ) * (j : ℝ) / Q = (j : ℝ) by field_simp]
      exact eC_int1122b j
    push_cast
    simp [this]
  · have hne : eC ((m : ℝ) / Q) ≠ 1 := by
      rw [Ne, eC_eq_one_iff1122b]; rintro ⟨j, hj⟩
      apply h; refine ⟨j, ?_⟩
      have : (m : ℝ) = Q * j := by
        rw [div_eq_iff hQ'] at hj; linarith
      exact_mod_cast this
    rw [geom_sum_eq hne, ← eC_nat_mul1122b,
      show (Q : ℝ) * ((m : ℝ) / Q) = (m : ℝ) by field_simp, eC_int1122b]
    simp

theorem dvd_iff_mod1122b (Q n c : ℕ) (hc : c < Q) : (Q : ℤ) ∣ (n : ℤ) - c ↔ n % Q = c := by
  rw [← Int.modEq_iff_dvd, Int.ModEq, ← Int.natCast_mod, ← Int.natCast_mod,
    Nat.mod_eq_of_lt hc]
  constructor <;> intro h <;> omega

/-! ### Helpers for the dual count -/

private theorem eC_re1122b (t : ℝ) : (eC t).re = Real.cos (2 * Real.pi * t) := by
  unfold eC
  have h : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) =
      (((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I_re]

private theorem eC_im1122b (t : ℝ) : (eC t).im = Real.sin (2 * Real.pi * t) := by
  unfold eC
  have h : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) =
      (((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I_im]

/-- `‖1 - e(t)‖ = 2 |sin π t|`. -/
private theorem norm_one_sub_eC1122b (t : ℝ) : ‖1 - eC t‖ = 2 * |Real.sin (Real.pi * t)| := by
  have hsq : ‖1 - eC t‖ ^ 2 = (2 * |Real.sin (Real.pi * t)|) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have h1 : (1 - eC t).re = 1 - Real.cos (2 * Real.pi * t) := by
      simp [eC_re1122b]
    have h2 : (1 - eC t).im = -Real.sin (2 * Real.pi * t) := by
      simp [eC_im1122b]
    rw [h1, h2]
    have hc := Real.cos_two_mul' (Real.pi * t)
    have hs := Real.sin_two_mul (Real.pi * t)
    have hsc := Real.sin_sq_add_cos_sq (Real.pi * t)
    rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring]
    have hsq1 : (2 * |Real.sin (Real.pi * t)|) ^ 2 = 4 * Real.sin (Real.pi * t) ^ 2 := by
      rw [mul_pow, sq_abs]; norm_num
    have h1c : 1 - Real.cos (2 * (Real.pi * t)) = 2 * Real.sin (Real.pi * t) ^ 2 := by
      linarith [hc, hsc]
    rw [h1c, hsq1, hs]
    nlinarith [hsc]
  have h1 : 0 ≤ ‖1 - eC t‖ := norm_nonneg _
  have h2 : 0 ≤ 2 * |Real.sin (Real.pi * t)| := by positivity
  nlinarith [hsq, h1, h2]

/-- For an integer `m` within `1/2` of `γ`, `2 |γ - m| ≤ |sin π γ|`. -/
private theorem two_mul_abs_sub_int_le_sin1122b {γ : ℝ} (m : ℤ)
    (hm : |γ - (m : ℝ)| ≤ 1 / 2) : 2 * |γ - (m : ℝ)| ≤ |Real.sin (Real.pi * γ)| := by
  set s : ℝ := γ - (m : ℝ) with hs
  have hγ : γ = (m : ℝ) + s := by rw [hs]; ring
  have hsin : Real.sin (Real.pi * γ) = (-1 : ℝ) ^ m * Real.sin (Real.pi * s) := by
    rw [hγ, show Real.pi * ((m : ℝ) + s) = Real.pi * s + (m : ℝ) * Real.pi by ring,
      Real.sin_add_int_mul_pi]
  have hx0 : 0 ≤ Real.pi * |s| := by positivity
  have hx1 : Real.pi * |s| ≤ Real.pi / 2 := by
    have h := abs_nonneg s
    nlinarith [Real.pi_pos, hm, h]
  have hmul := Real.mul_le_sin hx0 hx1
  have heq : 2 / Real.pi * (Real.pi * |s|) = 2 * |s| := by
    field_simp
  have hslo : -(1 / 2) ≤ s := (abs_le.mp hm).1
  have hshi : s ≤ 1 / 2 := (abs_le.mp hm).2
  have hsinabs : Real.sin (Real.pi * |s|) = |Real.sin (Real.pi * s)| := by
    rcases le_total 0 s with h | h
    · have hp : 0 ≤ Real.sin (Real.pi * s) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos, hshi])
      rw [abs_of_nonneg h, abs_of_nonneg hp]
    · have hp : Real.sin (Real.pi * s) ≤ 0 :=
        Real.sin_nonpos_of_nonpos_of_neg_pi_le (by nlinarith [Real.pi_pos, h])
          (by nlinarith [Real.pi_pos, hslo])
      rw [abs_of_nonpos h, mul_neg, Real.sin_neg, abs_of_nonpos hp]
  rw [hsin, abs_mul]
  have h1 : |((-1 : ℝ) ^ m)| = 1 := by
    rw [abs_zpow, abs_neg, abs_one, one_zpow]
  rw [h1, one_mul, ← hsinabs]
  linarith [hmul, heq.le, heq.ge]

/-- `‖Σ_{n < J} e(n x)‖ ≤ 1 / |sin π x|`. -/
private theorem norm_dirichlet1122b {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0) (J : ℕ) :
    ‖∑ k ∈ range J, eC ((k : ℝ) * x)‖ ≤ 1 / |Real.sin (Real.pi * x)| := by
  have hne_norm : ‖(1 : ℂ) - eC x‖ = 2 * |Real.sin (Real.pi * x)| := norm_one_sub_eC1122b x
  have hpos : 0 < 2 * |Real.sin (Real.pi * x)| := by
    have : |Real.sin (Real.pi * x)| ≠ 0 := abs_ne_zero.mpr hx
    positivity
  have hne : (1 : ℂ) - eC x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hne_norm
    linarith
  have h1e : eC x ≠ 1 := by
    intro h0
    exact hne (by rw [h0, sub_self])
  rw [Finset.sum_congr rfl (fun k (_ : k ∈ range J) => eC_nat_mul1122b k x)]
  rw [geom_sum_eq h1e]
  have hden : ‖eC x - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
    rw [← norm_neg, neg_sub, hne_norm]
  rw [norm_div, hden]
  have hnum : ‖(eC x) ^ J - 1‖ ≤ 2 := by
    calc ‖(eC x) ^ J - 1‖ ≤ ‖(eC x) ^ J‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, eC_norm1122b, norm_one]; norm_num
  calc ‖(eC x) ^ J - 1‖ / (2 * |Real.sin (Real.pi * x)|)
      ≤ 2 / (2 * |Real.sin (Real.pi * x)|) :=
        div_le_div_of_nonneg_right hnum hpos.le
    _ = 1 / |Real.sin (Real.pi * x)| := by field_simp

/-- The geometric sum bound over an order convex range of `ℕ`: for an integer `m` within `1/2`
of `γ`, `‖Σ_{n ∈ S} e(γ n)‖ · 2 |γ - m| ≤ 1`. -/
private theorem geom_interval1122b (S : Finset ℕ)
    (hconv : ∀ x ∈ S, ∀ z ∈ S, ∀ y, x ≤ y → y ≤ z → y ∈ S)
    (γ : ℝ) (m : ℤ) (hm : |γ - (m : ℝ)| ≤ 1 / 2) :
    ‖∑ n ∈ S, eC (γ * n)‖ * (2 * |γ - (m : ℝ)|) ≤ 1 := by
  set δ : ℝ := |γ - (m : ℝ)| with hδ
  have hδ0 : 0 ≤ δ := abs_nonneg _
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  set p := S.min' hne with hp
  set q := S.max' hne with hq
  have hpq : p ≤ q := Finset.min'_le S q (Finset.max'_mem S hne)
  have hSeq : S = Finset.Icc p q := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro n hn
      exact Finset.mem_Icc.2 ⟨Finset.min'_le S n hn, Finset.le_max' S n hn⟩
    · intro n hn
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
      exact hconv _ (Finset.min'_mem S hne) _ (Finset.max'_mem S hne) n h1 h2
  have hstep : ‖∑ n ∈ S, eC (γ * n)‖
      ≤ ‖∑ i ∈ range (q + 1 - p), (eC γ) ^ i‖ := by
    rw [hSeq, show Finset.Icc p q = Finset.Ico p (q + 1) by
      ext n; simp, Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ i : ℕ, eC (γ * ((p + i : ℕ) : ℝ)) =
        eC (γ * (p : ℝ)) * (eC γ) ^ i := by
      intro i
      rw [show γ * ((p + i : ℕ) : ℝ) = γ * (p : ℝ) + (i : ℝ) * γ by
        push_cast; ring, eC_add1122b, eC_nat_mul1122b]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ range (q + 1 - p)) => hterm i),
      ← Finset.mul_sum, norm_mul, eC_norm1122b, one_mul]
  rcases eq_or_lt_of_le hδ0 with h0 | hpos
  · rw [← h0, mul_zero]; norm_num
  have hsin : 2 * δ ≤ |Real.sin (Real.pi * γ)| := by
    rw [hδ]; exact two_mul_abs_sub_int_le_sin1122b m hm
  have hne1 : eC γ ≠ 1 := by
    intro h
    rw [eC_eq_one_iff1122b] at h
    obtain ⟨j, hj⟩ := h
    have hcast : ((j - m : ℤ) : ℝ) = γ - (m : ℝ) := by
      push_cast [hj]; ring
    have habs : |((j - m : ℤ) : ℝ)| ≤ 1 / 2 := by rw [hcast]; exact hm
    have hlt : ((|j - m| : ℤ) : ℝ) < 1 := by
      rw [Int.cast_abs]; linarith
    have hle0 : |j - m| ≤ 0 := by
      have h1 : |j - m| < (1 : ℤ) := by exact_mod_cast hlt
      omega
    have h2 : j - m = 0 := abs_eq_zero.mp (le_antisymm hle0 (abs_nonneg _))
    have hjm : j = m := by omega
    have hγm : γ = (m : ℝ) := by rw [hj, hjm]
    rw [hγm, sub_self, abs_zero] at hδ
    linarith [hδ]
  have hnum : ‖(eC γ) ^ (q + 1 - p) - 1‖ ≤ 2 := by
    calc ‖(eC γ) ^ (q + 1 - p) - 1‖
        ≤ ‖(eC γ) ^ (q + 1 - p)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, eC_norm1122b, norm_one]; norm_num
  have hden : ‖eC γ - 1‖ = 2 * |Real.sin (Real.pi * γ)| := by
    rw [← norm_neg, neg_sub, norm_one_sub_eC1122b]
  have hdenpos : 0 < ‖eC γ - 1‖ := by
    rw [hden]; have := hpos; nlinarith [Real.pi_pos]
  have hgeom : ‖∑ i ∈ range (q + 1 - p), (eC γ) ^ i‖
      ≤ 2 / (2 * |Real.sin (Real.pi * γ)|) := by
    rw [geom_sum_eq hne1, norm_div, hden]
    exact div_le_div_of_nonneg_right hnum (by rw [hden] at hdenpos; linarith)
  have hfin : 2 / (2 * |Real.sin (Real.pi * γ)|) ≤ 1 / (2 * δ) := by
    have hs : 0 < 2 * δ := by linarith
    have hsp : 0 < 2 * |Real.sin (Real.pi * γ)| := by linarith [hsin, hpos]
    rw [div_le_div_iff₀ hsp hs]
    nlinarith [hsin]
  have h2 : 1 / (2 * δ) * (2 * δ) = 1 := by field_simp
  calc ‖∑ n ∈ S, eC (γ * n)‖ * (2 * δ) ≤ (1 / (2 * δ)) * (2 * δ) := by
        apply mul_le_mul_of_nonneg_right (hstep.trans (hgeom.trans hfin)) (by linarith)
    _ = 1 := h2

/-- Integers with pairwise distances at most `L` number at most `L + 1`. -/
private theorem card_le_of_diam1122b (s : Finset ℕ) {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ x ∈ s, ∀ z ∈ s, |(x : ℝ) - (z : ℝ)| ≤ L) :
    (s.card : ℝ) ≤ L + 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [card_empty, Nat.cast_zero]
    linarith
  have hpq : s.min' hne ≤ s.max' hne := Finset.min'_le s (s.max' hne) (Finset.max'_mem s hne)
  have hsub : s ⊆ Finset.Icc (s.min' hne) (s.max' hne) := by
    intro n hn
    exact Finset.mem_Icc.2 ⟨Finset.min'_le s n hn, Finset.le_max' s n hn⟩
  have h1 : s.card ≤ s.max' hne + 1 - s.min' hne := by
    calc s.card ≤ (Finset.Icc (s.min' hne) (s.max' hne)).card := Finset.card_le_card hsub
      _ = s.max' hne + 1 - s.min' hne := Nat.card_Icc _ _
  have h2 : ((s.max' hne + 1 - s.min' hne : ℕ) : ℝ)
      = (s.max' hne : ℝ) + 1 - (s.min' hne : ℝ) := by
    rw [Nat.cast_sub (by omega : s.min' hne ≤ s.max' hne + 1)]
    push_cast
    ring
  have h3 : |(s.max' hne : ℝ) - (s.min' hne : ℝ)| ≤ L :=
    h _ (Finset.max'_mem s hne) _ (Finset.min'_mem s hne)
  have h4 : (s.max' hne : ℝ) - (s.min' hne : ℝ) ≤ L := (abs_le.mp h3).2
  calc (s.card : ℝ) ≤ ((s.max' hne + 1 - s.min' hne : ℕ) : ℝ) := by exact_mod_cast h1
    _ = (s.max' hne : ℝ) + 1 - (s.min' hne : ℝ) := h2
    _ ≤ L + 1 := by linarith

/-- The `Q` frequencies `a/Q - β`, `a < Q`, are spaced `1/Q` apart: at most `6 t Q + 3` of them
lie within `t` of an integer, for `0 < t ≤ 1/2`. -/
private theorem count_dual1122b (Q : ℕ) (hQ : 1 ≤ Q) (β : ℝ) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1 / 2) :
    (((Finset.range Q).filter (fun a : ℕ => ∃ k : ℤ, |(a : ℝ) / Q - β - (k : ℝ)| ≤ t)).card : ℝ)
      ≤ 6 * t * Q + 3 := by
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  set ξ : ℝ := (Q : ℝ) * β with hξ
  set k₀ : ℤ := ⌊ξ / Q⌋ with hk₀
  set y : ℝ := ξ - (k₀ : ℝ) * Q with hy
  have hy0 : 0 ≤ y := by
    have h := Int.floor_le (ξ / Q)
    rw [hy]
    have : (⌊ξ / Q⌋ : ℝ) * Q ≤ (ξ / Q) * Q := by
      exact mul_le_mul_of_nonneg_right h (le_of_lt hQpos)
    rw [div_mul_cancel₀ ξ (ne_of_gt hQpos)] at this
    linarith
  have hy1 : y < Q := by
    have h := Int.lt_floor_add_one (ξ / Q)
    rw [hy]
    have h2 : (ξ / Q) * Q < ((⌊ξ / Q⌋ : ℝ) + 1) * Q := by
      exact mul_lt_mul_of_pos_right h hQpos
    rw [div_mul_cancel₀ ξ (ne_of_gt hQpos)] at h2
    linarith
  set A₁ : Finset ℕ := (Finset.range Q).filter (fun a : ℕ => |(a : ℝ) - y| ≤ t * Q) with hA₁
  set A₂ : Finset ℕ :=
    (Finset.range Q).filter (fun a : ℕ => |(a : ℝ) - (y + Q)| ≤ t * Q) with hA₂
  set A₃ : Finset ℕ :=
    (Finset.range Q).filter (fun a : ℕ => |(a : ℝ) - (y - Q)| ≤ t * Q) with hA₃
  have hsub : (Finset.range Q).filter
      (fun a : ℕ => ∃ k : ℤ, |(a : ℝ) / Q - β - (k : ℝ)| ≤ t) ⊆ A₁ ∪ (A₂ ∪ A₃) := by
    intro a ha
    obtain ⟨haQ, k, hk⟩ := Finset.mem_filter.mp ha
    have hltQ : a < Q := by simpa using haQ
    have haQ' : (a : ℝ) < (Q : ℝ) := by exact_mod_cast hltQ
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    have h1 : |(a : ℝ) - ξ - (k : ℝ) * Q| ≤ t * Q := by
      have hmul : ((a : ℝ) / Q - β - (k : ℝ)) * Q = (a : ℝ) - ξ - (k : ℝ) * Q := by
        rw [hξ]
        field_simp
      rw [← hmul, abs_mul, abs_of_pos hQpos]
      exact mul_le_mul_of_nonneg_right hk (le_of_lt hQpos)
    set K : ℤ := k + k₀ with hK
    have h2 : |(a : ℝ) - y - (K : ℝ) * Q| ≤ t * Q := by
      have heq : (a : ℝ) - y - (K : ℝ) * Q = (a : ℝ) - ξ - (k : ℝ) * Q := by
        have hKr : (K : ℝ) = (k : ℝ) + (k₀ : ℝ) := by
          rw [hK]; push_cast; ring
        rw [hKr, hy]
        ring
      rw [heq]; exact h1
    have htQ : t * Q ≤ (Q : ℝ) / 2 := by nlinarith [ht1]
    have hlow := (abs_le.mp h2).1
    have hupp := (abs_le.mp h2).2
    have hKlo : -(Q : ℝ) - (Q : ℝ) / 2 ≤ (K : ℝ) * Q := by
      nlinarith [hupp, htQ, hy1, ha0]
    have hle1 : (a : ℝ) + 1 ≤ (Q : ℝ) := by
      exact_mod_cast (show a + 1 ≤ Q by omega)
    have hKhi : (K : ℝ) * Q ≤ (Q : ℝ) - 1 + (Q : ℝ) / 2 := by
      nlinarith [hlow, htQ, hy0, hle1]
    have hKge : (-1 : ℤ) ≤ K := by
      by_contra hcon
      have hKle : K ≤ -2 := by omega
      have hKr : (K : ℝ) ≤ -2 := by exact_mod_cast hKle
      nlinarith [hKlo, hKr, hQpos, hQ1]
    have hKle1 : K ≤ 1 := by
      by_contra hcon
      have hKge2 : (2 : ℤ) ≤ K := by omega
      have hKr : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hKge2
      nlinarith [hKhi, hKr, hQpos, hQ1]
    have hm₁ : a ∈ A₁ ∨ a ∈ A₂ ∨ a ∈ A₃ := by
      interval_cases K
      · right; right
        refine Finset.mem_filter.mpr ⟨haQ, ?_⟩
        have hKr : ((-1 : ℤ) : ℝ) = -1 := by push_cast; ring
        have heq : (a : ℝ) - (y - Q) = (a : ℝ) - y - ((-1 : ℤ) : ℝ) * Q := by
          rw [hKr]; ring
        rw [heq]; exact h2
      · left
        refine Finset.mem_filter.mpr ⟨haQ, ?_⟩
        have hKr : ((0 : ℤ) : ℝ) = 0 := by push_cast; ring
        have heq : (a : ℝ) - y = (a : ℝ) - y - ((0 : ℤ) : ℝ) * Q := by
          rw [hKr]; ring
        rw [heq]; exact h2
      · right; left
        refine Finset.mem_filter.mpr ⟨haQ, ?_⟩
        have hKr : ((1 : ℤ) : ℝ) = 1 := by push_cast; ring
        have heq : (a : ℝ) - (y + Q) = (a : ℝ) - y - ((1 : ℤ) : ℝ) * Q := by
          rw [hKr]; ring
        rw [heq]; exact h2
    rcases hm₁ with h' | h' | h'
    · exact Finset.mem_union_left _ h'
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ h')
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ h')
  have hdiam : ∀ (c : ℝ), ((Finset.range Q).filter (fun a : ℕ => |(a : ℝ) - c| ≤ t * Q)).card
      ≤ 2 * t * Q + 1 := by
    intro c
    exact card_le_of_diam1122b _ (by positivity) (by
      intro x hx z hz
      have hx' : |(x : ℝ) - c| ≤ t * Q := (Finset.mem_filter.mp hx).2
      have hz' : |(z : ℝ) - c| ≤ t * Q := (Finset.mem_filter.mp hz).2
      have h4 : |(x : ℝ) - (z : ℝ)| ≤ |(x : ℝ) - c| + |c - (z : ℝ)| := abs_sub_le _ _ _
      have h5 : |c - (z : ℝ)| = |(z : ℝ) - c| := abs_sub_comm _ _
      rw [h5] at h4
      linarith)
  have hA₁ : (A₁.card : ℝ) ≤ 2 * t * Q + 1 := hdiam y
  have hA₂ : (A₂.card : ℝ) ≤ 2 * t * Q + 1 := hdiam (y + Q)
  have hA₃ : (A₃.card : ℝ) ≤ 2 * t * Q + 1 := hdiam (y - Q)
  have hstep1 : (((Finset.range Q).filter (fun a : ℕ => ∃ k : ℤ,
      |(a : ℝ) / Q - β - (k : ℝ)| ≤ t)).card : ℝ) ≤ ((A₁ ∪ (A₂ ∪ A₃)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hstep2 : ((A₁ ∪ (A₂ ∪ A₃)).card : ℝ) ≤ (A₁.card : ℝ) + ((A₂ ∪ A₃).card : ℝ) := by
    exact_mod_cast Finset.card_union_le A₁ (A₂ ∪ A₃)
  have hstep3 : ((A₂ ∪ A₃).card : ℝ) ≤ (A₂.card : ℝ) + (A₃.card : ℝ) := by
    exact_mod_cast Finset.card_union_le A₂ A₃
  linarith

/-! ### The new leaf -/

/-- LEAF: the Fourier dual count of a linear exponential sum over an interval, the step of
Matomäki and Shao Lemma 7.4 behind the error `Q C² √N` of Lemma 5.2, page 18. Class MEDIUM.
For an interval `S` of length at most `N`, `|∑_{n ∈ S} e(γ n)| ≤ min(|S|, 1/(2‖γ‖))`, and
summing over the `Q` frequencies `a/Q - β` gives at most `2N + Q (1 + log Q)`, which is at most
`K (N + Q √N)` once `6 Q² ≤ N`. -/
theorem twisted_interval_bound : ∃ K : ℝ, 0 < K ∧ ∀ N Q : ℕ, 1 ≤ Q → 6 * Q ^ 2 ≤ N →
    ∀ S : Finset ℕ, S ⊆ range N → (∀ x ∈ S, ∀ z ∈ S, ∀ y, x ≤ y → y ≤ z → y ∈ S) →
    ∀ β : ℝ, ∑ a ∈ range Q, ‖∑ n ∈ S, eC (((a : ℝ) / Q - β) * n)‖ ≤
      K * (N + Q * Real.sqrt N) := by
  refine ⟨100, by norm_num, ?_⟩
  intro N Q hQ hNQ S hsub hconv β
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hN6 : 6 ≤ N := by
    have h1 : 6 * 1 ≤ 6 * Q ^ 2 := by
      have : 1 ≤ Q ^ 2 := by nlinarith
      nlinarith
    omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  set M : ℝ := Real.sqrt N with hMdef
  have hMM : M * M = (N : ℝ) := by
    rw [hMdef]; exact Real.mul_self_sqrt (le_of_lt hNpos)
  have hMpos : 0 < M := by
    rw [hMdef]
    exact Real.sqrt_pos.mpr hNpos
  have hM2 : 2 ≤ M := by
    rw [hMdef]
    have : (2 : ℝ) ^ 2 ≤ (N : ℝ) := by
      have : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 4 ≤ N)
      nlinarith
    exact Real.le_sqrt_of_sq_le this
  set t₀ : ℝ := 1 / (2 * M) with ht₀
  have ht₀pos : 0 < t₀ := by rw [ht₀]; positivity
  have ht₀half : t₀ ≤ 1 / 2 := by
    rw [ht₀, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have ht₀M : t₀ * M = 1 / 2 := by
    rw [ht₀]; field_simp
  set X : ℕ → ℝ := fun a => (a : ℝ) / Q - β with hX
  set Δ : ℕ → ℝ := fun a => |X a - (round (X a) : ℝ)| with hΔ
  have hΔle : ∀ a, Δ a ≤ 1 / 2 := fun a => abs_sub_round (X a)
  -- the cardinality of the frequencies near an integer
  have hcard : ((range Q).filter (fun a : ℕ => Δ a ≤ t₀)).card ≤ 6 * t₀ * Q + 3 := by
    have heq : (range Q).filter (fun a : ℕ => Δ a ≤ t₀)
        = (range Q).filter (fun a : ℕ => ∃ k : ℤ, |(a : ℝ) / Q - β - (k : ℝ)| ≤ t₀) := by
      refine Finset.filter_congr fun a _ => ?_
      constructor
      · intro h
        exact ⟨round (X a), h⟩
      · rintro ⟨k, hk⟩
        exact le_trans (round_le (X a) k) hk
    rw [heq]
    exact count_dual1122b Q hQ β ht₀pos ht₀half
  -- the pointwise bound
  have hpt : ∀ a : ℕ, ‖∑ n ∈ S, eC (X a * n)‖ ≤ if Δ a ≤ t₀ then (N : ℝ) else M := by
    intro a
    by_cases h : Δ a ≤ t₀
    · rw [if_pos h]
      have h1 : ‖∑ n ∈ S, eC (X a * n)‖ ≤ (S.card : ℝ) := by
        calc ‖∑ n ∈ S, eC (X a * n)‖ ≤ ∑ n ∈ S, ‖eC (X a * n)‖ := norm_sum_le _ _
          _ = (S.card : ℝ) := by simp [eC_norm1122b]
      have h2 : (S.card : ℝ) ≤ (N : ℝ) := by
        have h3 : S.card ≤ N := by
          calc S.card ≤ (range N).card := Finset.card_le_card hsub
            _ = N := Finset.card_range N
        exact_mod_cast h3
      linarith
    · rw [if_neg h]
      have hlt : t₀ < Δ a := not_le.mp h
      have hpos : 0 < Δ a := lt_trans ht₀pos hlt
      have hg := geom_interval1122b S hconv (X a) (round (X a)) (hΔle a)
      have h2δ : 0 < 2 * Δ a := by linarith
      have hb : ‖∑ n ∈ S, eC (X a * n)‖ ≤ 1 / (2 * Δ a) := by
        rw [le_div_iff₀ h2δ]
        linarith [hg]
      have hfin : 1 / (2 * Δ a) ≤ 1 / (2 * t₀) := by
        apply one_div_le_one_div_of_le (by linarith)
        linarith
      have hMeq : 1 / (2 * t₀) = M := by
        rw [ht₀]; field_simp
      linarith [hb, hfin, hMeq.le, hMeq.ge]
  -- the split by the threshold
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range Q)
    (fun a : ℕ => Δ a ≤ t₀) (fun a : ℕ => ‖∑ n ∈ S, eC (X a * n)‖)
  have hpart1 : ∑ a ∈ (range Q).filter (fun a : ℕ => Δ a ≤ t₀),
      ‖∑ n ∈ S, eC (X a * n)‖ ≤ (6 * t₀ * Q + 3) * N := by
    have h1 : ∑ a ∈ (range Q).filter (fun a : ℕ => Δ a ≤ t₀),
        ‖∑ n ∈ S, eC (X a * n)‖
        ≤ ∑ a ∈ (range Q).filter (fun a : ℕ => Δ a ≤ t₀), (N : ℝ) := by
      refine Finset.sum_le_sum fun a ha => ?_
      have hh := hpt a
      rwa [if_pos (Finset.mem_filter.mp ha).2] at hh
    have h2 : ∑ a ∈ (range Q).filter (fun a : ℕ => Δ a ≤ t₀), (N : ℝ)
        = (((range Q).filter (fun a : ℕ => Δ a ≤ t₀)).card : ℝ) * N := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 : (((range Q).filter (fun a : ℕ => Δ a ≤ t₀)).card : ℝ) ≤ 6 * t₀ * Q + 3 := by
      exact_mod_cast hcard
    have hNnn : (0 : ℝ) ≤ N := le_of_lt hNpos
    calc ∑ a ∈ (range Q).filter (fun a : ℕ => Δ a ≤ t₀), ‖∑ n ∈ S, eC (X a * n)‖
        ≤ (((range Q).filter (fun a : ℕ => Δ a ≤ t₀)).card : ℝ) * N := by rw [← h2]; exact h1
      _ ≤ (6 * t₀ * Q + 3) * N := by
          apply mul_le_mul_of_nonneg_right h3 hNnn
  have hpart2 : ∑ a ∈ (range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀),
      ‖∑ n ∈ S, eC (X a * n)‖ ≤ (Q : ℝ) * M := by
    have h1 : ∑ a ∈ (range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀),
        ‖∑ n ∈ S, eC (X a * n)‖
        ≤ ∑ a ∈ (range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀), M := by
      refine Finset.sum_le_sum fun a ha => ?_
      have hh := hpt a
      rwa [if_neg (Finset.mem_filter.mp ha).2] at hh
    have h2 : ∑ a ∈ (range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀), M
        = (((range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀)).card : ℝ) * M := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 : ((range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀)).card ≤ Q := by
      calc ((range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀)).card ≤ (range Q).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
        _ = Q := Finset.card_range Q
    have h3' : (((range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀)).card : ℝ) ≤ (Q : ℝ) := by
      exact_mod_cast h3
    have hMnn : (0 : ℝ) ≤ M := le_of_lt hMpos
    calc ∑ a ∈ (range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀), ‖∑ n ∈ S, eC (X a * n)‖
        ≤ (((range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀)).card : ℝ) * M := by
          rw [← h2]; exact h1
      _ ≤ (Q : ℝ) * M := by
          apply mul_le_mul_of_nonneg_right h3' hMnn
  have htotal : ∑ a ∈ range Q, ‖∑ n ∈ S, eC (X a * n)‖ ≤ (6 * t₀ * Q + 3) * N + Q * M := by
    rw [← hsplit]
    linarith [hpart1, hpart2]
  have hkey : 6 * t₀ * (Q : ℝ) * N = 3 * (Q : ℝ) * M := by
    have hNeq : (N : ℝ) = M * M := hMM.symm
    have h1 : t₀ * M = 1 / 2 := ht₀M
    rw [hNeq]
    -- 6 * t₀ * Q * (M * M) = 3 * Q * M
    have : 6 * t₀ * (Q : ℝ) * (M * M) = 3 * (Q : ℝ) * M * (2 * (t₀ * M)) := by ring
    rw [this, h1]
    ring
  have hfin1 : (6 * t₀ * (Q : ℝ) + 3) * (N : ℝ) + (Q : ℝ) * M
      = 4 * ((Q : ℝ) * M) + 3 * (N : ℝ) := by
    calc (6 * t₀ * (Q : ℝ) + 3) * (N : ℝ) + (Q : ℝ) * M
        = 6 * t₀ * (Q : ℝ) * (N : ℝ) + 3 * (N : ℝ) + (Q : ℝ) * M := by ring
      _ = 3 * ((Q : ℝ) * M) + 3 * (N : ℝ) + (Q : ℝ) * M := by rw [hkey]; ring
      _ = 4 * ((Q : ℝ) * M) + 3 * (N : ℝ) := by ring
  have hQnn : (0 : ℝ) ≤ (Q : ℝ) := le_of_lt hQpos
  have hMnn : (0 : ℝ) ≤ M := le_of_lt hMpos
  calc ∑ a ∈ range Q, ‖∑ n ∈ S, eC (X a * ↑n)‖
      ≤ 4 * ((Q : ℝ) * M) + 3 * (N : ℝ) := htotal.trans (le_of_eq hfin1)
    _ ≤ 100 * ((N : ℝ) + (Q : ℝ) * Real.sqrt N) := by
        rw [show Real.sqrt N = M from hMdef.symm]
        nlinarith [hQnn, hMnn, hNpos.le]

/-! ### The coefficient bound from the premise on `𝒬` -/

theorem coef_bound1122b (Q : ℕ) (𝒬 : Finset ℕ) (η₀ : ℝ)
    (hexp : ∀ q a : ℕ, q ∣ Q → q ≠ 1 → 0 < a → a.Coprime q →
        ‖∑ c₀ ∈ 𝒬, eC ((a : ℝ) * c₀ / q)‖ ≤ η₀ * #𝒬)
    (a : ℕ) (ha0 : 0 < a) (haQ : a < Q) :
    ‖∑ c ∈ 𝒬, eC (-((a : ℝ) * c / Q))‖ ≤ η₀ * #𝒬 := by
  set g := Nat.gcd a Q with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ ha0
  have hga : g ∣ a := Nat.gcd_dvd_left a Q
  have hgQ : g ∣ Q := Nat.gcd_dvd_right a Q
  have hcop : (a / g).Coprime (Q / g) := Nat.coprime_div_gcd_div_gcd hgpos
  have hqdvd : Q / g ∣ Q := Nat.div_dvd_of_dvd hgQ
  have hapos : 0 < a / g := Nat.div_pos (Nat.le_of_dvd ha0 hga) hgpos
  have hq1 : Q / g ≠ 1 := by
    intro h1
    have hQg : Q = g := by
      have := Nat.mul_div_cancel' hgQ
      rw [h1, mul_one] at this; exact this.symm
    have : g ≤ a := Nat.le_of_dvd ha0 hga
    omega
  have hbound := hexp (Q / g) (a / g) hqdvd hq1 hapos hcop
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hQpos : 0 < Q := by omega
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQpos.ne'
  have hconv : ∀ c : ℕ, ((a / g : ℕ) : ℝ) * c / ((Q / g : ℕ) : ℝ) = (a : ℝ) * c / Q := by
    intro c
    rw [Nat.cast_div hga hgR, Nat.cast_div hgQ hgR]
    field_simp
  simp_rw [hconv] at hbound
  have hc : ∑ c ∈ 𝒬, eC (-((a : ℝ) * c / Q)) =
      (starRingEnd ℂ) (∑ c ∈ 𝒬, eC ((a : ℝ) * c / Q)) := by
    rw [map_sum]; simp_rw [eC_conj1122b]
  rw [hc, Complex.norm_conj]
  exact hbound

/-! ### The general lemma -/

/-- Lemma 5.2, page 18, on any order convex range `R N ⊆ range N`, from the leaf
`twisted_interval_bound`. -/
theorem lemma52On_of_twisted (R : ℕ → Finset ℕ) (hsub : ∀ N, R N ⊆ range N)
    (hconv : ∀ N, ∀ x ∈ R N, ∀ z ∈ R N, ∀ y, x ≤ y → y ≤ z → y ∈ R N)
    (htw : ∃ K : ℝ, 0 < K ∧ ∀ N Q : ℕ, 1 ≤ Q → 6 * Q ^ 2 ≤ N →
      ∀ S : Finset ℕ, S ⊆ range N → (∀ x ∈ S, ∀ z ∈ S, ∀ y, x ≤ y → y ≤ z → y ∈ S) →
      ∀ β : ℝ, ∑ a ∈ range Q, ‖∑ n ∈ S, eC (((a : ℝ) / Q - β) * n)‖ ≤
        K * (N + Q * Real.sqrt N)) :
    Lemma52On R := by
  obtain ⟨K, hK, hKb⟩ := htw
  refine ⟨2 * K, by positivity, ?_⟩
  intro Cc χ hχ0 hχC N Q hQ hNQ 𝒬 h𝒬 hne η₀ hη₀ hexp t
  obtain ⟨cf, α, hcf, hχ⟩ := hχC
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQR : (Q : ℝ) ≠ 0 := hQpos.ne'
  have h𝒬pos : (0 : ℝ) < #𝒬 := by exact_mod_cast hne.card_pos
  set S := R N with hS
  set f : ℕ → ℝ := fun n => χ (t - n) with hf
  -- the twisted sums
  set T : ℕ → ℂ := fun a => ∑ n ∈ S, (f n : ℂ) * eC ((a : ℝ) * n / Q) with hT
  set G : Fin Cc → ℕ → ℂ := fun k a => ∑ n ∈ S, eC (((a : ℝ) / Q - α k) * n) with hG
  have hTexp : ∀ a, T a = ∑ k, cf k * eC (α k * t) * G k a := by
    intro a
    simp only [hT, hG, hf, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hχ (t - n), Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, mul_assoc, ← eC_add1122b, ← eC_add1122b]
    congr 2
    push_cast
    ring
  have hTnorm : ∀ a, ‖T a‖ ≤ ∑ k, (Cc : ℝ) * ‖G k a‖ := by
    intro a
    rw [hTexp a]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul, eC_norm1122b, mul_one]
    exact mul_le_mul_of_nonneg_right (hcf k) (norm_nonneg _)
  have hTsum : ∑ a ∈ range Q, ‖T a‖ ≤ (Cc : ℝ) * (Cc * (K * (N + Q * Real.sqrt N))) := by
    calc ∑ a ∈ range Q, ‖T a‖ ≤ ∑ a ∈ range Q, ∑ k, (Cc : ℝ) * ‖G k a‖ :=
          Finset.sum_le_sum fun a _ => hTnorm a
      _ = (Cc : ℝ) * ∑ k, ∑ a ∈ range Q, ‖G k a‖ := by
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
      _ ≤ (Cc : ℝ) * ∑ _k : Fin Cc, K * (N + Q * Real.sqrt N) := by
          gcongr with k
          exact hKb N Q hQ hNQ S (hsub N) (hconv N) (α k)
      _ = (Cc : ℝ) * (Cc * (K * (N + Q * Real.sqrt N))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the expansion of the class indicator
  set coef : ℕ → ℂ := fun a => ∑ c ∈ 𝒬, eC (-((a : ℝ) * c / Q)) with hcoef
  set F : ℝ := ∑ c₀ ∈ 𝒬, ∑ n ∈ S.filter (fun n => n % Q = c₀), f n with hF
  have hexpand : ((Q : ℝ) * F : ℂ) = ∑ a ∈ range Q, coef a * T a := by
    have h1 : F = ∑ n ∈ S, ∑ c ∈ 𝒬, if n % Q = c then f n else 0 := by
      rw [hF]
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
    have h2 : ∑ a ∈ range Q, coef a * T a =
        ∑ a ∈ range Q, ∑ n ∈ S, ∑ c ∈ 𝒬,
          (f n : ℂ) * eC ((a : ℝ) * (((n : ℤ) - c : ℤ) : ℝ) / Q) := by
      simp only [hcoef, hT, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun n _ =>
        Finset.sum_congr rfl fun c _ => ?_
      have hadd := eC_add1122b ((a : ℝ) * n / Q) (-((a : ℝ) * c / Q))
      rw [show ((a : ℝ) * (((n : ℤ) - c : ℤ) : ℝ) / Q) = (a : ℝ) * n / Q + -((a : ℝ) * c / Q) by
        push_cast; ring, hadd]
      ring
    have h3 : ∑ a ∈ range Q, ∑ n ∈ S, ∑ c ∈ 𝒬,
          (f n : ℂ) * eC ((a : ℝ) * (((n : ℤ) - c : ℤ) : ℝ) / Q) =
        ∑ n ∈ S, ∑ c ∈ 𝒬, (f n : ℂ) *
          ∑ a ∈ range Q, eC ((a : ℝ) * (((n : ℤ) - c : ℤ) : ℝ) / Q) := by
      simp_rw [Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_comm]
    have h4 : ∀ n ∈ S, ∀ c ∈ 𝒬, (f n : ℂ) *
          ∑ a ∈ range Q, eC ((a : ℝ) * (((n : ℤ) - c : ℤ) : ℝ) / Q) =
        (f n : ℂ) * (if n % Q = c then (Q : ℂ) else 0) := by
      intro n _ c hc
      have hcQ : c < Q := Finset.mem_range.1 (h𝒬 hc)
      rw [orth1122b Q hQ]
      by_cases h : n % Q = c
      · rw [if_pos ((dvd_iff_mod1122b Q n c hcQ).2 h), if_pos h]
      · rw [if_neg (mt (dvd_iff_mod1122b Q n c hcQ).1 h), if_neg h]
    rw [h2, h3, h1, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [h4 n hn c hc]
    split_ifs <;> simp; ring
  -- the frequency `a = 0`
  have h0 : coef 0 * T 0 = (((#𝒬 : ℝ) * ∑ n ∈ S, f n : ℝ) : ℂ) := by
    simp [hcoef, hT, eC]
  have hQmem : 0 ∈ range Q := Finset.mem_range.2 (by omega)
  have hre : (Q : ℝ) * F = (#𝒬 : ℝ) * (∑ n ∈ S, f n) +
      (∑ a ∈ (range Q).erase 0, coef a * T a).re := by
    have := congrArg Complex.re hexpand
    have hcast : ((Q : ℝ) : ℂ) * (F : ℂ) = (((Q : ℝ) * F : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.ofReal_re, ← Finset.add_sum_erase _ _ hQmem, Complex.add_re, h0,
      Complex.ofReal_re] at this
    exact this
  have hrest : -(η₀ * #𝒬 * ∑ a ∈ range Q, ‖T a‖) ≤
      (∑ a ∈ (range Q).erase 0, coef a * T a).re := by
    have hn : ‖∑ a ∈ (range Q).erase 0, coef a * T a‖ ≤ η₀ * #𝒬 * ∑ a ∈ range Q, ‖T a‖ := by
      calc ‖∑ a ∈ (range Q).erase 0, coef a * T a‖
          ≤ ∑ a ∈ (range Q).erase 0, ‖coef a * T a‖ := norm_sum_le _ _
        _ ≤ ∑ a ∈ (range Q).erase 0, η₀ * #𝒬 * ‖T a‖ := by
            refine Finset.sum_le_sum fun a ha => ?_
            rw [norm_mul]
            have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
            have haQ : a < Q := Finset.mem_range.1 (Finset.mem_of_mem_erase ha)
            exact mul_le_mul_of_nonneg_right
              (coef_bound1122b Q 𝒬 η₀ hexp a (Nat.pos_of_ne_zero ha0) haQ) (norm_nonneg _)
        _ = η₀ * #𝒬 * ∑ a ∈ (range Q).erase 0, ‖T a‖ := by rw [Finset.mul_sum]
        _ ≤ η₀ * #𝒬 * ∑ a ∈ range Q, ‖T a‖ := by
            gcongr
            exact Finset.erase_subset _ _
    have := Complex.abs_re_le_norm (∑ a ∈ (range Q).erase 0, coef a * T a)
    have := neg_abs_le (∑ a ∈ (range Q).erase 0, coef a * T a).re
    linarith
  -- arithmetic
  have hNR : ((6 * Q ^ 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hNQ
  push_cast at hNR
  have hQs : (Q : ℝ) * Real.sqrt N ≤ N := by
    have hq : (Q : ℝ) ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by nlinarith)
    calc (Q : ℝ) * Real.sqrt N ≤ Real.sqrt N * Real.sqrt N :=
          mul_le_mul_of_nonneg_right hq (Real.sqrt_nonneg _)
      _ = N := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hstep : η₀ * ∑ a ∈ range Q, ‖T a‖ ≤ 2 * K * (η₀ * (Cc : ℝ) ^ 2 * N) := by
    calc η₀ * ∑ a ∈ range Q, ‖T a‖ ≤ η₀ * ((Cc : ℝ) * (Cc * (K * (N + Q * Real.sqrt N)))) :=
          mul_le_mul_of_nonneg_left hTsum hη₀.le
      _ ≤ η₀ * ((Cc : ℝ) * (Cc * (K * (N + N)))) := by gcongr
      _ = 2 * K * (η₀ * (Cc : ℝ) ^ 2 * N) := by ring
  have hextra : 0 ≤ 2 * K * ((Q : ℝ) * (Cc : ℝ) ^ 2 * Real.sqrt N) := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ h𝒬pos]
  nlinarith [mul_le_mul_of_nonneg_left hstep h𝒬pos.le, mul_nonneg h𝒬pos.le hextra]

/-! ### The two ranges are order convex -/

theorem dyad_convex1122b (N : ℕ) :
    ∀ x ∈ dyad N, ∀ z ∈ dyad N, ∀ y, x ≤ y → y ≤ z → y ∈ dyad N := by
  intro x hx z hz y hxy hyz
  simp only [dyad, Finset.mem_filter, Finset.mem_range] at hx hz ⊢
  have hxy' : (x : ℝ) ≤ y := by exact_mod_cast hxy
  have hyz' : (y : ℝ) ≤ z := by exact_mod_cast hyz
  exact ⟨by omega, by linarith [hx.2.1], by linarith [hz.2.2]⟩

theorem half_convex1122b (N : ℕ) :
    ∀ x ∈ half N, ∀ z ∈ half N, ∀ y, x ≤ y → y ≤ z → y ∈ half N := by
  intro x hx z hz y hxy hyz
  simp only [half, Finset.mem_filter, Finset.mem_range] at hx hz ⊢
  have hxy' : (x : ℝ) ≤ y := by exact_mod_cast hxy
  have hyz' : (y : ℝ) ≤ z := by exact_mod_cast hyz
  exact ⟨by omega, by linarith [hx.2.1], by linarith [hz.2.2]⟩

/-! ### The assemblies -/

/-- `lemma52_dyad` from the leaf `twisted_interval_bound`. -/
theorem lemma52_dyad_of_leaves : Lemma52On dyad :=
  lemma52On_of_twisted dyad (fun _ => Finset.filter_subset _ _) dyad_convex1122b
    twisted_interval_bound

/-- `lemma52_half` from the leaf `twisted_interval_bound`. -/
theorem lemma52_half_of_leaves : Lemma52On half :=
  lemma52On_of_twisted half (fun _ => Finset.filter_subset _ _) half_convex1122b
    twisted_interval_bound


end Lemma52Port

/-! ### The leaves -/

/-- LEAF: Proposition 5.1, page 18, for `n ∼ N/3`. Class HARD. Its proof occupies Sections 6 to
10, the weighted semilinear sieve Theorem 6.5 and the circle method, through the reduction to
(7.1) on page 30. -/
theorem prop51_dyad : Prop51On dyad := by sorry

/-- LEAF: Proposition 5.1, page 18, with `N/3 < n < N/2` in place of `n ∼ N/3`, the variant
behind the remark on page 11. Class HARD. Not printed: the paper's Proposition 5.1 is for
dyadic `n ∼ N` only, and Sections 6 to 10 are claimed to work for this interval as well. -/
theorem prop51_half : Prop51On half := by sorry

/-- LEAF: Lemma 5.2, page 18, which cites Matomäki and Shao Lemma 7.4, for `n ∼ N/3`.
Class MEDIUM. -/
theorem lemma52_dyad : Lemma52On dyad := Lemma52Port.lemma52_dyad_of_leaves

/-- LEAF: Lemma 5.2, page 18, which cites Matomäki and Shao Lemma 7.4, for `N/3 < n < N/2`.
Class MEDIUM. Matomäki and Shao Lemma 7.4 is an equidistribution in residue classes
whose proof works on any interval. -/
theorem lemma52_half : Lemma52On half := Lemma52Port.lemma52_half_of_leaves

/-- LEAF: Lemma 5.3, page 19, display (5.4), proved on pages 20 to 21 from Lemma 5.4 and (5.2).
Class MEDIUM. -/
theorem lemma53 : Lemma53 := Lemma53Port.lemma53_of_leaves

/-- The remark (5.2), page 18: `|𝒬| > 0`. A residue with `W c₀ + b ≡ 2` modulo every prime
`p ∣ Q`, `p ∤ W`, lies in `𝒬`; at the primes `p ∣ W` amenability does the work. -/
theorem qres_nonempty : QResNonempty := by
  intro J w _ _ b hamen Q hQ
  obtain ⟨_, h216, hbW, hb1, -⟩ := hamen
  set W : ℤ := WW J w
  set S : Finset ℕ := Q.primeFactors.filter (fun p : ℕ => ¬ (p : ℤ) ∣ W)
  set P : ℤ := ∏ p ∈ S, (p : ℤ)
  have hcop : IsCoprime W P := by
    apply IsCoprime.prod_right
    intro p hp
    obtain ⟨hpQ, hpW⟩ := mem_filter.mp hp
    have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Nat.prime_of_mem_primeFactors hpQ)
    exact ((Prime.coprime_iff_not_dvd hpp).mpr hpW).symm
  obtain ⟨u, v, huv⟩ := hcop
  set x : ℤ := u * (2 - b)
  have hQ0 : (Q : ℤ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  set c : ℤ := x % Q
  have hc0 : 0 ≤ c := Int.emod_nonneg x hQ0
  have hcQ : c < Q := Int.emod_lt_of_pos x (by exact_mod_cast (show 0 < Q by omega))
  have hct : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg hc0
  have key : W * c + b = 2 - P * (v * (2 - b)) - (Q : ℤ) * (W * (x / Q)) := by
    simp only [c, Int.emod_def]
    linear_combination (2 - b) * huv
  have h2W : (2 : ℤ) ∣ W := dvd_trans (by norm_num) h216
  -- a prime `p ∣ Q`, `p ∤ W` divides `P`
  have hPdvd : ∀ p : ℕ, p.Prime → p ∣ Q → ¬ (p : ℤ) ∣ W → (p : ℤ) ∣ P := by
    intro p hp hpQ hpW
    apply dvd_prod_of_mem
    exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpQ, by omega⟩, hpW⟩
  have hQd : ∀ p : ℕ, p ∣ Q → (p : ℤ) ∣ (Q : ℤ) := fun p h => by exact_mod_cast h
  refine ⟨c.toNat, ?_⟩
  simp only [QRes, mem_filter, mem_range]
  refine ⟨by omega, ?_, ?_⟩
  · rw [hct, Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
    apply Nat.coprime_of_dvd
    intro p hp h1 h2
    have hpi : (p : ℤ) ∣ W * c + b := Int.ofNat_dvd_left.mpr h1
    have hpQ : p ∣ Q := by simpa using h2
    have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    by_cases hpW : (p : ℤ) ∣ W
    · have hpb : (p : ℤ) ∣ b := by
        have := dvd_sub hpi (dvd_mul_of_dvd_left hpW c)
        simpa using this
      exact hpp.not_isUnit (hbW.isUnit_of_dvd' hpb hpW)
    · have hP := hPdvd p hp hpQ hpW
      have h2 : (p : ℤ) ∣ 2 := by
        have := dvd_add (dvd_add hpi (dvd_mul_of_dvd_left hP (v * (2 - b))))
          (dvd_mul_of_dvd_left (hQd p hpQ) (W * (x / Q)))
        rwa [key, show 2 - P * (v * (2 - b)) - (Q : ℤ) * (W * (x / Q)) +
          P * (v * (2 - b)) + (Q : ℤ) * (W * (x / Q)) = 2 by ring] at this
      have h2' : p ∣ 2 := by exact_mod_cast h2
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2'
      subst hp2
      exact hpW (by exact_mod_cast h2W)
  · intro p hp h4 h3 hpQ hdiv
    rw [hct] at hdiv
    by_cases hpW : (p : ℤ) ∣ W
    · apply hb1 p hp h4 h3 hpW
      have := dvd_sub hdiv (dvd_mul_of_dvd_left hpW c)
      rwa [show W * c + b - 1 - W * c = b - 1 by ring] at this
    · have hP := hPdvd p hp hpQ hpW
      have h1 : (p : ℤ) ∣ 1 := by
        have := dvd_add (dvd_add hdiv (dvd_mul_of_dvd_left hP (v * (2 - b))))
          (dvd_mul_of_dvd_left (hQd p hpQ) (W * (x / Q)))
        rwa [key, show 2 - P * (v * (2 - b)) - (Q : ℤ) * (W * (x / Q)) - 1 +
          P * (v * (2 - b)) + (Q : ℤ) * (W * (x / Q)) = 1 by ring] at this
      exact (Nat.prime_iff_prime_int.mp hp).not_isUnit (isUnit_of_dvd_one h1)

/-! ### Assembly -/

/-- `(log N)^r` is eventually at most `√N / K`. -/
theorem eventually_log_rpow_le_sqrt (K r : ℝ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → K * Real.log N ^ r ≤ Real.sqrt N := by
  have hc : (0 : ℝ) < 1 / (|K| + 1) := by positivity
  have h := ((isLittleO_log_rpow_rpow_atTop r (by norm_num : (0 : ℝ) < 1 / 2)).bound hc)
  have h' := tendsto_natCast_atTop_atTop.eventually h
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp h'
  refine ⟨N₁, fun N hN => ?_⟩
  have hb := hN₁ N hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsq : Real.sqrt N = (N : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hN0 _)] at hb
  rw [hsq]
  have hK1 : 0 < |K| + 1 := by positivity
  calc K * Real.log N ^ r ≤ |K| * |Real.log N ^ r| := by
        calc K * Real.log N ^ r ≤ |K * Real.log N ^ r| := le_abs_self _
          _ = |K| * |Real.log N ^ r| := abs_mul _ _
    _ ≤ (|K| + 1) * |Real.log N ^ r| := by
        apply mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ ≤ (|K| + 1) * (1 / (|K| + 1) * (N : ℝ) ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hb hK1.le
    _ = (N : ℝ) ^ ((1 : ℝ) / 2) := by field_simp

/-- Splitting into residue classes `c₀ ∈ 𝒬 ⊆ [0, Q)` loses nothing for nonnegative terms. -/
theorem sum_residue_le (s 𝒬 : Finset ℕ) (Q : ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    ∑ c ∈ 𝒬, ∑ n ∈ s.filter (fun n => n % Q = c), f n ≤ ∑ n ∈ s, f n := by
  have h1 : ∑ c ∈ 𝒬, ∑ n ∈ s.filter (fun n => n % Q = c), f n =
      ∑ n ∈ s.filter (fun n => n % Q ∈ 𝒬), f n := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := s.filter (fun n => n % Q ∈ 𝒬)) (t := 𝒬)
      (g := fun n => n % Q) (fun n hn => (mem_filter.mp hn).2)]
    apply sum_congr rfl
    intro c hc
    apply sum_congr _ (fun _ _ => rfl)
    ext n
    simp only [mem_filter]
    constructor
    · rintro ⟨hn, rfl⟩; exact ⟨⟨hn, hc⟩, rfl⟩
    · rintro ⟨⟨hn, -⟩, h⟩; exact ⟨hn, h⟩
  rw [h1]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n _ _ => hf n)

/-- Generic assembly: `Prop32On R` from Proposition 5.1 and Lemmas 5.2, 5.3 on `R`, for a
range `R N` inside `(N/3, 2N/3)` up to one point. -/
theorem prop32On_of_split (R : ℕ → Finset ℕ)
    (hR : ∀ N : ℕ, ∃ m : ℕ, ∀ n ∈ R N, n ≠ m → (N : ℝ) / 3 < n ∧ (n : ℝ) < 2 * N / 3)
    (h51 : Prop51On R) (h52 : Lemma52On R) (h53 : Lemma53) (hne : QResNonempty) :
    Prop32On R := by
  obtain ⟨δ₁, hδ₁, H51⟩ := h51
  obtain ⟨C', hC', H52⟩ := h52
  refine ⟨δ₁, C' + 3, hδ₁, by linarith, ?_⟩
  intro Cc J w hJ hw hCw
  obtain ⟨B, HB⟩ := H51 Cc
  have hw1 : (1 : ℝ) ≤ w := by
    have : (1 : ℝ) ≤ wBig := Real.one_le_rpow (by norm_num) (by positivity)
    linarith
  have hw0 : (0 : ℝ) < w := by linarith
  set u : ℝ := (w : ℝ) ^ ((1 : ℝ) / 3) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hw0 _
  have hε : 0 < 1 / u := by positivity
  obtain ⟨N₀', HN⟩ := HB J w hJ hw hCw (1 / u) hε
  obtain ⟨N₁, A1⟩ := eventually_log_rpow_le_sqrt (C' * (Cc : ℝ) ^ 2 * u) (B : ℝ)
  obtain ⟨N₂, A2⟩ := eventually_log_rpow_le_sqrt (Real.sqrt 6) (B : ℝ)
  obtain ⟨N₃, A3⟩ := eventually_log_rpow_le_sqrt ((Cc : ℝ) ^ 2 * u / δ₁) ((3 : ℝ) / 2)
  refine ⟨max (max N₀' 1) (max N₁ (max N₂ N₃)), ?_⟩
  intro χ hχ0 hχC b hb0 hbW hamen N hN t ht1 ht2
  have hN0' : N₀' ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1' : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNN₂ : N₂ ≤ N := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hN
  have hNN₃ : N₃ ≤ N := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hN
  obtain ⟨Q, hQ1, hQB, HQ⟩ := HN χ hχ0 hχC N hN0'
  set W : ℤ := WW J w with hW
  set 𝒬 := QRes Q W b with h𝒬
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1'
  have hNr0 : (0 : ℝ) ≤ N := by linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
  have h𝒬ne : 𝒬.Nonempty := hne J w hJ hw b hamen Q hQ1
  have h𝒬pos : (0 : ℝ) < #𝒬 := by exact_mod_cast h𝒬ne.card_pos
  have hsqN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNr0
  have hsqN1 : Real.sqrt N ≤ N := by
    have h1 : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hNr
    nlinarith
  have hlogB : Real.log N ^ (B : ℝ) = Real.log N ^ B := Real.rpow_natCast _ _
  -- 6 Q² ≤ N
  have h6 : 6 * Q ^ 2 ≤ N := by
    have a2 := A2 N hNN₂
    rw [hlogB] at a2
    have hp0 : 0 ≤ Real.log N ^ B := pow_nonneg hlog0 _
    have hs6 : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
    have : (6 : ℝ) * Q ^ 2 ≤ N := by
      have hQ2 : (Q : ℝ) ^ 2 ≤ (Real.log N ^ B) ^ 2 := pow_le_pow_left₀ (by linarith) hQB 2
      have hsq0 : 0 ≤ Real.sqrt 6 * Real.log N ^ B := by positivity
      have := mul_self_le_mul_self hsq0 a2
      nlinarith
    exact_mod_cast this
  -- Lemma 5.3 supplies the premise of Lemma 5.2 with `η₀ = w^{-1/2}`.
  have hη : (0 : ℝ) < (w : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hw0 _
  have H2 := H52 Cc χ hχ0 hχC N Q hQ1 h6 𝒬 (filter_subset _ _) h𝒬ne _ hη
    (fun q a hq hq1 ha hco => h53 J w hJ hw b hamen Q q a hQ1 hq hq1 ha hco) t
  -- sum Proposition 5.1 over `c₀ ∈ 𝒬`
  have htabs : |(t : ℝ)| ≤ 5 * (N : ℝ) / 3 := abs_le.mpr ⟨by linarith, by linarith⟩
  set wt : ℝ := Real.log N ^ ((3 : ℝ) / 2) *
    ((Nat.totient W.toNat : ℝ) / W) ^ ((3 : ℝ) / 2) with hwt
  set T : ℕ → ℝ := fun c => ∑ n ∈ (R N).filter (fun n => n % Q = c), χ (t - n) with hT
  set G : ℝ := ∑ n ∈ (R N).filter (fun n : ℕ => Good (W * (n : ℤ) + b)), χ (t - n) with hG
  have hsum : ∑ c ∈ 𝒬, δ₁ * ((Q : ℝ) / #𝒬) * (T c - 1 / u * N / Q) ≤
      ∑ c ∈ 𝒬, wt * ∑ n ∈ ((R N).filter (fun n : ℕ => Good (W * (n : ℤ) + b))).filter
        (fun n => n % Q = c), χ (t - n) :=
    sum_le_sum (fun c hc => HQ b hb0 hbW hamen t htabs c hc)
  have hW1 : (1 : ℤ) ≤ W := hamen.1
  have hWr : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW1
  have hphi0 : (0 : ℝ) ≤ (Nat.totient W.toNat : ℝ) / W := by positivity
  have hphi1 : (Nat.totient W.toNat : ℝ) / W ≤ 1 := by
    rw [div_le_one (by linarith)]
    have h1 : (Nat.totient W.toNat : ℝ) ≤ (W.toNat : ℝ) := by
      exact_mod_cast Nat.totient_le _
    have h2 : ((W.toNat : ℕ) : ℝ) = (W : ℝ) := by
      have : ((W.toNat : ℕ) : ℤ) = W := Int.toNat_of_nonneg (by linarith)
      exact_mod_cast this
    linarith
  have hwt0 : 0 ≤ wt := mul_nonneg (Real.rpow_nonneg hlog0 _) (Real.rpow_nonneg hphi0 _)
  have hwtle : wt ≤ Real.log N ^ ((3 : ℝ) / 2) := by
    have := Real.rpow_le_one hphi0 hphi1 (by norm_num : (0 : ℝ) ≤ 3 / 2)
    calc wt ≤ Real.log N ^ ((3 : ℝ) / 2) * 1 :=
          mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hlog0 _)
      _ = _ := mul_one _
  have hL : ∑ c ∈ 𝒬, δ₁ * ((Q : ℝ) / #𝒬) * (T c - 1 / u * N / Q) =
      δ₁ * ((Q : ℝ) / #𝒬 * ∑ c ∈ 𝒬, T c - 1 / u * N) := by
    rw [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul]
    field_simp
  have hRgt : ∑ c ∈ 𝒬, wt * ∑ n ∈ ((R N).filter (fun n : ℕ => Good (W * (n : ℤ) + b))).filter
        (fun n => n % Q = c), χ (t - n) ≤ wt * G := by
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left
      (sum_residue_le _ 𝒬 Q (fun n => χ (t - n)) (fun n => hχ0 _)) hwt0
  -- boundary point
  obtain ⟨m, hm⟩ := hR N
  have hχb : ∀ n, χ n ≤ (Cc : ℝ) ^ 2 := fun n => (le_abs_self _).trans
    (fourierComplexity_abs_le hχC n)
  have hF : wt * G - wt * (Cc : ℝ) ^ 2 ≤ ∑ n ∈ R N, fW W b N n * χ (t - n) := by
    have hpt : ∀ n ∈ R N, wt * (if Good (W * (n : ℤ) + b) then χ (t - n) else 0) -
        (if n = m then wt * (Cc : ℝ) ^ 2 else 0) ≤ fW W b N n * χ (t - n) := by
      intro n hn
      by_cases hnm : n = m
      · have hfW : 0 ≤ fW W b N n := by unfold fW; split_ifs <;> [exact hwt0; exact le_refl _]
        have h1 : wt * (if Good (W * (n : ℤ) + b) then χ (t - n) else 0) ≤ wt * (Cc : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hwt0
          split_ifs
          · exact hχb _
          · positivity
        rw [if_pos hnm]
        have := mul_nonneg hfW (hχ0 (t - n))
        linarith
      · obtain ⟨ha, hb'⟩ := hm n hn hnm
        rw [if_neg hnm, sub_zero]
        unfold fW
        by_cases hg : Good (W * (n : ℤ) + b)
        · rw [if_pos hg, if_pos ⟨ha, hb', hg⟩]
        · rw [if_neg hg, if_neg (fun h => hg h.2.2)]; simp
    have hs := sum_le_sum hpt
    rw [sum_sub_distrib, ← mul_sum, ← sum_filter, sum_ite_eq'] at hs
    have : (if m ∈ R N then wt * (Cc : ℝ) ^ 2 else 0) ≤ wt * (Cc : ℝ) ^ 2 := by
      split_ifs
      · exact le_refl _
      · positivity
    linarith
  -- the three error terms
  have hCc2 : (Cc : ℝ) ^ 2 * u ≤ (w : ℝ) ^ ((1 : ℝ) / 2) := by
    have hc0 : (0 : ℝ) ≤ Cc := Nat.cast_nonneg _
    have e1 : (Cc : ℝ) ^ 2 = ((Cc : ℝ) ^ 20) ^ ((1 : ℝ) / 10) := by
      rw [← Real.rpow_natCast (Cc : ℝ) 20, ← Real.rpow_mul hc0,
        show ((20 : ℕ) : ℝ) * (1 / 10) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have e2 : ((Cc : ℝ) ^ 20) ^ ((1 : ℝ) / 10) ≤ (w : ℝ) ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow (by positivity) hCw (by norm_num)
    have e3 : (w : ℝ) ^ ((1 : ℝ) / 10) * u = (w : ℝ) ^ ((1 : ℝ) / 10 + 1 / 3) := by
      rw [hu, ← Real.rpow_add hw0]
    have e4 : (w : ℝ) ^ ((1 : ℝ) / 10 + 1 / 3) ≤ (w : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hw1 (by norm_num)
    rw [e1]
    calc ((Cc : ℝ) ^ 20) ^ ((1 : ℝ) / 10) * u ≤ (w : ℝ) ^ ((1 : ℝ) / 10) * u :=
          mul_le_mul_of_nonneg_right e2 hu0.le
      _ ≤ _ := by rw [e3]; exact e4
  have hη1 : (w : ℝ) ^ (-(1 : ℝ) / 2) * (w : ℝ) ^ ((1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hw0]; norm_num
  have E1 : (w : ℝ) ^ (-(1 : ℝ) / 2) * (Cc : ℝ) ^ 2 * N ≤ 1 / u * N := by
    have : (w : ℝ) ^ (-(1 : ℝ) / 2) * (Cc : ℝ) ^ 2 * u ≤ 1 := by
      calc (w : ℝ) ^ (-(1 : ℝ) / 2) * (Cc : ℝ) ^ 2 * u
          = (w : ℝ) ^ (-(1 : ℝ) / 2) * ((Cc : ℝ) ^ 2 * u) := by ring
        _ ≤ (w : ℝ) ^ (-(1 : ℝ) / 2) * (w : ℝ) ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hCc2 hη.le
        _ = 1 := hη1
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hu0]
    nlinarith
  have E2 : C' * ((Q : ℝ) * (Cc : ℝ) ^ 2 * Real.sqrt N) ≤ 1 / u * N := by
    have a1 := A1 N hNN₁
    rw [hlogB] at a1
    have hsq0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    have : C' * (Cc : ℝ) ^ 2 * u * Q ≤ Real.sqrt N :=
      le_trans (mul_le_mul_of_nonneg_left hQB (by positivity)) a1
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hu0]
    calc C' * ((Q : ℝ) * (Cc : ℝ) ^ 2 * Real.sqrt N) * u
        = (C' * (Cc : ℝ) ^ 2 * u * Q) * Real.sqrt N := by ring
      _ ≤ Real.sqrt N * Real.sqrt N := mul_le_mul_of_nonneg_right this hsq0
      _ = N := hsqN
  have E3 : wt * (Cc : ℝ) ^ 2 ≤ δ₁ * (1 / u * N) := by
    have a3 := A3 N hNN₃
    have h1 : (Cc : ℝ) ^ 2 * u / δ₁ * Real.log N ^ ((3 : ℝ) / 2) ≤ N := le_trans a3 hsqN1
    have h2 : wt * (Cc : ℝ) ^ 2 ≤ Real.log N ^ ((3 : ℝ) / 2) * (Cc : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hwtle (by positivity)
    have h3 : Real.log N ^ ((3 : ℝ) / 2) * (Cc : ℝ) ^ 2 ≤ δ₁ * (1 / u * N) := by
      have : Real.log N ^ ((3 : ℝ) / 2) * (Cc : ℝ) ^ 2 =
          ((Cc : ℝ) ^ 2 * u / δ₁ * Real.log N ^ ((3 : ℝ) / 2)) * (δ₁ / u) := by
        field_simp
      rw [this]
      calc ((Cc : ℝ) ^ 2 * u / δ₁ * Real.log N ^ ((3 : ℝ) / 2)) * (δ₁ / u)
          ≤ N * (δ₁ / u) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = δ₁ * (1 / u * N) := by ring
    linarith
  -- combine
  have hS := H2
  have hkey : C' * ((w : ℝ) ^ (-(1 : ℝ) / 2) * (Cc : ℝ) ^ 2 * N + Q * (Cc : ℝ) ^ 2 * Real.sqrt N)
      + 1 / u * N ≤ (C' + 2) * (1 / u * N) := by
    have := mul_le_mul_of_nonneg_left E1 hC'.le
    have e := mul_add C' ((w : ℝ) ^ (-(1 : ℝ) / 2) * (Cc : ℝ) ^ 2 * N)
      ((Q : ℝ) * (Cc : ℝ) ^ 2 * Real.sqrt N)
    linarith only [this, e, E2]
  have hmain : δ₁ * ((∑ n ∈ R N, χ (t - n)) - (C' + 2) * (1 / u * N)) ≤ wt * G := by
    have h1 : δ₁ * ((∑ n ∈ R N, χ (t - n)) - (C' + 2) * (1 / u * N)) ≤
        δ₁ * ((Q : ℝ) / #𝒬 * ∑ c ∈ 𝒬, T c - 1 / u * N) := by
      apply mul_le_mul_of_nonneg_left _ hδ₁.le
      linarith only [H2, hkey]
    linarith only [h1, hsum, hL, hRgt]
  have hfinal : (C' + 3) * N / u = (C' + 2) * (1 / u * N) + 1 / u * N := by
    field_simp; ring
  rw [hfinal]
  linarith only [hmain, hF, E3]

/-- Proposition 3.2, page 9, from the leaves of Section 5. -/
theorem paper_weighted_prime_input_of_leaves : Prop32 := by
  apply prop32On_of_split dyad _ prop51_dyad lemma52_dyad lemma53 qres_nonempty
  intro N
  refine ⟨Nat.ceil ((N : ℝ) / 3), fun n hn hnm => ?_⟩
  simp only [dyad, mem_filter] at hn
  refine ⟨lt_of_le_of_ne hn.2.1 ?_, hn.2.2⟩
  intro h
  apply hnm
  rw [h, Nat.ceil_natCast]

/-- The half interval variant of Proposition 3.2, page 11, from the leaves of Section 5. -/
theorem paper_half_interval_input_of_leaves : Prop32Half := by
  apply prop32On_of_split half _ prop51_half lemma52_half lemma53 qres_nonempty
  intro N
  refine ⟨0, fun n hn _ => ?_⟩
  simp only [half, mem_filter] at hn
  refine ⟨hn.2.1, ?_⟩
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith [hn.2.2]

end LeanLab.Teravainen2016

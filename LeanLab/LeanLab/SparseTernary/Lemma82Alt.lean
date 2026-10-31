/-
P0086 Basak, Bhat, Dong, Zaharescu 2024, arXiv 2409.08968 v1, Section 8, display (8.1), Lemma 8.2.
`Lemma82` of MajorArcs.lean PROVED unconditionally, as `lemma82`, for every `m`, odd or not.
An independent second proof: unit U-1338 proved the same Prop in Lemma82.lean on the PC first;
this file was written without seeing that one and uses a different grouping, kept as a cross-check.

Plain math, our own route, not the paper's induction. Write `n = q_0`, `k = n / w` for `w ∣ n`.
1. `inner_eq`. For `w ∣ q_0`, by (8.1) `q_ℓ = q_0 / (q_0, a k + ℓ)`. Shifting `ℓ ↦ b = a k + ℓ mod q_0`,
   `inner(w, a) = Σ_{r ∈ R_0} e(a r / w) K(r)` with `K(r) = Σ_{b < q_0} μ(d_b)/φ(d_b) e(-b r / q_0)`,
   `d_b = q_0 / (q_0, b)`. Grouping `b` by `d_b` (`farey`): `K(r) = Σ_{d ∣ q_0} μ(d)/φ(d) c_d(r)`, a divisor
   sum of a multiplicative function, so for `(r, q_0) = 1` it is `∏_{p < Z} (1 + 1/(p-1)) = ∏ p/(p-1)`
   (`Ksum`, from `ram_mul`, `ram_prime` of LocalFactors.lean and Mathlib's `map_prod_of_prime`).
2. `fq_eq`. Hence `f(w) = κ³ q_0⁻³ Σ_{t ∈ R_0³} Σ_{(a,w)=1} e(a (r₁+r₂+r₃-m)/w)`, `κ = ∏ p/(p-1)`.
3. `Gq0_eq_card`. Summing over `w ∣ q_0`, `farey` again turns `Σ_w Σ_{(a,w)=1} e(a s / w)` into
   `Σ_{b < q_0} e(b s / q_0)`, which is `q_0` if `q_0 ∣ s` and `0` otherwise (`sum_range_ee`).
   So `G(q_0) = κ³ q_0⁻² #{t ∈ R_0³ : r₁+r₂+r₃ ≡ m mod q_0}`.
4. `card_triples`. By CRT that count is `∏_{p < Z} N_p(m)`.
5. `lemma82_eq`. `κ³ q_0⁻² ∏ N_p = ∏ p N_p(m)/(p-1)³`, the closed form `Gprod`.
At `Z = 3`, `q_0 = 2`, this is the prime local evaluation `G(2) = 2 N_2(m)`; in general the factor
`p N_p(m)/(p-1)³` of the product is the local evaluation `G(p)`, and no separate prime case is needed.
Odd `m` is not used: for even `m`, `N_2(m) = 0` and both sides vanish.

Consequences: `majorLower_of_analytic`, `MajorLower A B (9A+1)` CONDITIONAL ON `Major618 A B` and
`Tail72 A B` only; `repProp_of_analytic`, `RepProp A` CONDITIONAL ON `Minor516W A B`,
`Major618 A B`, `Tail72 A B` only.

AI-written Lean code, Claude, run 20261021T0503Z-11296, unit U-1351. Checked only by the Lean
kernel. Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.SparseTernary.LocalFactors

open Finset Filter Real
open scoped Classical

noncomputable section
namespace LeanLab.SparseTernary.Lemma82Proof

open LeanLab.SparseTernary LeanLab.SparseTernary.Section4 LeanLab.SparseTernary.MajorArcs
open LeanLab.SparseTernary.LocalFactors

/-! ### Exponential sums -/

theorem ee_eq_one {x : ℝ} (h : ee x = 1) : ∃ n : ℤ, x = n := by
  unfold ee at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨n, ?_⟩
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h2 : ((x : ℝ) : ℂ) = (n : ℂ) := by
    have := hn; rw [mul_comm (n : ℂ)] at this
    exact mul_left_cancel₀ hpi this
  exact_mod_cast h2

/-- Orthogonality mod `n`: `Σ_{b < n} e(b s / n) = n` if `n ∣ s`, else `0`. -/
theorem sum_range_ee (n : ℕ) (hn : 0 < n) (s : ℤ) :
    ∑ b ∈ range n, ee ((b : ℝ) * s / n) = if (n : ℤ) ∣ s then (n : ℂ) else 0 := by
  set ζ := ee ((s : ℝ) / n) with hζ
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpow : ∀ b : ℕ, ee ((b : ℝ) * s / n) = ζ ^ b := by
    intro b; rw [hζ, ← ee_nat_mul]; congr 1; ring
  rw [sum_congr rfl (fun b _ => hpow b)]
  split_ifs with hd
  · obtain ⟨c, hc⟩ := hd
    have h1 : ζ = 1 := by
      rw [hζ, hc, show (((n : ℤ) * c : ℤ) : ℝ) / n = ((c : ℤ) : ℝ) by push_cast; field_simp]
      exact ee_int c
    simp [h1]
  · have hζp : ζ ^ n = 1 := by
      rw [hζ, ← ee_nat_mul, show (n : ℝ) * ((s : ℝ) / n) = ((s : ℤ) : ℝ) by field_simp]
      exact ee_int s
    have hζ1 : ζ ≠ 1 := by
      intro h
      obtain ⟨k, hk⟩ := ee_eq_one h
      apply hd
      refine ⟨k, ?_⟩
      have : (s : ℝ) = n * k := by rw [div_eq_iff hn0] at hk; rw [hk]; ring
      exact_mod_cast this
    rw [geom_sum_eq hζ1, hζp, sub_self, zero_div]

theorem gcd_mod (n x : ℕ) : Nat.gcd n (x % n) = Nat.gcd n x := by
  rw [Nat.gcd_comm, ← Nat.gcd_rec]

/-- **Farey grouping**: the fractions `b/n`, `0 ≤ b < n`, are exactly the reduced fractions `c/d`
with `d ∣ n`, `1 ≤ c ≤ d`, `(c, d) = 1`, and `d = n/(n, b)`. For any weight `ψ` and integer `x`,
`Σ_{d ∣ n} ψ(d) Σ_{(c,d)=1} e(c x/d) = Σ_{b < n} ψ(n/(n,b)) e(b x/n)`. -/
theorem farey (n : ℕ) (hn : 0 < n) (ψ : ℕ → ℂ) (x : ℤ) :
    ∑ d ∈ n.divisors, ψ d * ∑ c ∈ U d, ee ((c : ℝ) * x / d) =
      ∑ b ∈ range n, ψ (n / Nat.gcd n b) * ee ((b : ℝ) * x / n) := by
  have e0 : ∑ d ∈ n.divisors, ψ d * ∑ c ∈ U d, ee ((c : ℝ) * x / d) =
      ∑ dc ∈ n.divisors.sigma U, ψ dc.1 * ee ((dc.2 : ℝ) * x / dc.1) := by
    rw [sum_sigma]; simp_rw [mul_sum]
  rw [e0]
  let φ : (Σ _ : ℕ, ℕ) → ℕ := fun dc => (dc.2 * (n / dc.1)) % n
  have hgcd : ∀ dc ∈ n.divisors.sigma U, n / Nat.gcd n (φ dc) = dc.1 := by
    rintro ⟨d, c⟩ hdc
    rw [mem_sigma] at hdc
    obtain ⟨hd, hc⟩ := hdc
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    obtain ⟨k, hk⟩ := hdn
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk; omega
      · exact h
    have hcop : c.Coprime d := (mem_filter.mp hc).2
    simp only [φ]
    rw [gcd_mod, hk, Nat.mul_div_cancel_left _ hd0, Nat.gcd_mul_right, Nat.gcd_comm,
      hcop.gcd_eq_one, one_mul, Nat.mul_div_cancel _ hk0]
  have hmem : ∀ dc ∈ n.divisors.sigma U, φ dc ∈ range n :=
    fun dc _ => mem_range.mpr (Nat.mod_lt _ hn)
  have hinj : ∀ a ∈ n.divisors.sigma U, ∀ b ∈ n.divisors.sigma U, φ a = φ b → a = b := by
    intro a ha b hb h
    have h1 : a.1 = b.1 := by rw [← hgcd a ha, ← hgcd b hb, h]
    obtain ⟨d, c⟩ := a
    obtain ⟨d', c'⟩ := b
    simp only at h1
    subst h1
    have ha' := mem_sigma.mp ha
    have hb' := mem_sigma.mp hb
    obtain ⟨k, hk⟩ := Nat.dvd_of_mem_divisors ha'.1
    have hd0 : 0 < d := Nat.pos_of_mem_divisors ha'.1
    have hk0 : k ≠ 0 := by rintro rfl; rw [mul_zero] at hk; omega
    have hkd : n / d = k := by rw [hk, Nat.mul_div_cancel_left _ hd0]
    simp only [φ, hkd] at h
    have hm : c * k ≡ c' * k [MOD d * k] := by rw [← hk]; exact h
    have hc := U_eq_of_modEq ha'.2 hb'.2 (Nat.ModEq.mul_right_cancel' hk0 hm)
    simp only at hc
    subst hc
    rfl
  have hcard : #(range n) ≤ #(n.divisors.sigma U) := by
    rw [card_sigma, card_range]
    simp_rw [card_U]
    rw [Nat.sum_totient]
  have hsurj := surj_on_of_inj_on_of_card_le (fun dc _ => φ dc) hmem
    (fun a b ha hb h => hinj a ha b hb h) hcard
  refine sum_bij (fun dc _ => φ dc) hmem (fun a ha b hb h => hinj a ha b hb h)
    (fun b hb => by obtain ⟨a, ha, h⟩ := hsurj b hb; exact ⟨a, ha, h.symm⟩) ?_
  rintro ⟨d, c⟩ hdc
  rw [hgcd _ hdc]
  congr 1
  have ha' := mem_sigma.mp hdc
  obtain ⟨k, hk⟩ := Nat.dvd_of_mem_divisors ha'.1
  have hd0 : 0 < d := Nat.pos_of_mem_divisors ha'.1
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk; omega
    · exact h
  have hkd : n / d = k := by rw [hk, Nat.mul_div_cancel_left _ hd0]
  simp only [φ, hkd]
  set t := (c * k) / n
  have e1 : (c * k) % n + n * t = c * k := Nat.mod_add_div _ _
  have e1' : (((c * k) % n : ℕ) : ℝ) = (c : ℝ) * k - n * t := by
    have := congrArg (Nat.cast (R := ℝ)) e1; push_cast at this; linarith
  have hnR : (n : ℝ) = d * k := by rw [hk]; push_cast; ring
  have hd0' : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hk0' : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
  have key : (c : ℝ) * x / d = (((c * k) % n : ℕ) : ℝ) * x / n + (((t : ℤ) * x : ℤ) : ℝ) := by
    rw [e1', hnR]; push_cast; field_simp; ring
  rw [key, ee_add, ee_int, mul_one]

/-- Shifting the summation variable mod `n`. -/
theorem sum_shift (n c : ℕ) (hn : 0 < n) (h : ℕ → ℂ) :
    ∑ ℓ ∈ range n, h ((c + ℓ) % n) = ∑ b ∈ range n, h b := by
  have hmem : ∀ ℓ ∈ range n, (c + ℓ) % n ∈ range n :=
    fun ℓ _ => mem_range.mpr (Nat.mod_lt _ hn)
  have hinj : ∀ a ∈ range n, ∀ b ∈ range n, (c + a) % n = (c + b) % n → a = b := by
    intro a ha b hb e
    have h' : a ≡ b [MOD n] := Nat.ModEq.add_left_cancel' c e
    rw [mem_range] at ha hb
    unfold Nat.ModEq at h'; rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'
  have hsurj := surj_on_of_inj_on_of_card_le (fun ℓ _ => (c + ℓ) % n) hmem
    (fun a b ha hb e => hinj a ha b hb e) le_rfl
  exact sum_bij (fun ℓ _ => (c + ℓ) % n) hmem (fun a ha b hb e => hinj a ha b hb e)
    (fun b hb => by obtain ⟨a, ha, e⟩ := hsurj b hb; exact ⟨a, ha, e.symm⟩) (fun _ _ => rfl)

/-! ### The constant `K(r) = Σ_{d ∣ q_0} μ(d)/φ(d) c_d(r) = ∏ p/(p-1)` -/

/-- `κ = ∏_{p < Z} p/(p-1) = q_0/φ(q_0)`. -/
def kap (Z : ℕ) : ℝ := ∏ p ∈ Nat.primesBelow Z, (p : ℝ) / ((p : ℝ) - 1)

/-- `d ↦ μ(d)/φ(d) · c_d(r)` as an arithmetic function. -/
def mr (r : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun d => (muphi d : ℂ) * ram d r, by simp [muphi]⟩

theorem mr_apply (r d : ℕ) : mr r d = (muphi d : ℂ) * ram d r := rfl

theorem muphi_mul {v w : ℕ} (h : v.Coprime w) : muphi (v * w) = muphi v * muphi w := by
  unfold muphi
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h, Nat.totient_mul h]
  push_cast; rw [mul_div_mul_comm]

theorem mr_mult (r : ℕ) : (mr r).IsMultiplicative := by
  refine ⟨?_, fun {v w} h => ?_⟩
  · rw [mr_apply, ram_one]; simp [muphi]
  rw [mr_apply, mr_apply, mr_apply]
  rcases Nat.eq_zero_or_pos v with rfl | hv0
  · rw [Nat.coprime_zero_left] at h; subst h; simp [muphi, ram_one]
  rcases Nat.eq_zero_or_pos w with rfl | hw0
  · rw [Nat.coprime_zero_right] at h; subst h; simp [muphi, ram_one]
  rw [ram_mul v w r hv0 hw0 h, muphi_mul h]; push_cast; ring

/-- **`K(r) = q_0/φ(q_0)`** for `(r, q_0) = 1`. -/
theorem Ksum (Z r : ℕ) (hr : r.Coprime (q0 Z)) :
    ∑ d ∈ (q0 Z).divisors, (muphi d : ℂ) * ram d r = ((kap Z : ℝ) : ℂ) := by
  have hm := (mr_mult r).mul (ArithmeticFunction.isMultiplicative_zeta.natCast (R := ℂ))
  have e1 : ∑ d ∈ (q0 Z).divisors, (muphi d : ℂ) * ram d r =
      (mr r * (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) (q0 Z) := by
    rw [ArithmeticFunction.coe_mul_zeta_apply]; rfl
  rw [e1]
  unfold q0
  rw [hm.map_prod_of_prime _ (fun p hp => Nat.prime_of_mem_primesBelow hp)]
  unfold kap
  push_cast
  refine prod_congr rfl fun p hp => ?_
  have hpp := Nat.prime_of_mem_primesBelow hp
  have hnd : ¬ p ∣ r := by
    have h1 : r.Coprime p := Nat.Coprime.coprime_dvd_right (dvd_q0 hp) hr
    exact (Nat.Prime.coprime_iff_not_dvd hpp).mp (Nat.coprime_comm.mp h1)
  rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.Prime.sum_divisors hpp, mr_apply, mr_apply,
    ram_prime p r hpp, if_neg hnd, ram_one]
  unfold muphi
  rw [ArithmeticFunction.moebius_apply_prime hpp, Nat.totient_prime hpp,
    ArithmeticFunction.moebius_apply_one, Nat.totient_one]
  have h1 : (p : ℂ) - 1 ≠ 0 := by
    intro h
    have hp1 : (p : ℂ) = 1 := by linear_combination h
    have h' : p = 1 := by exact_mod_cast hp1
    exact hpp.one_lt.ne' h'
  push_cast [Nat.cast_sub hpp.one_le]
  field_simp
  ring

/-! ### Step 1: the inner sum -/

/-- **`inner(w, a) = κ Σ_{r ∈ R_0} e(a r / w)`** for `w ∣ q_0`. -/
theorem inner_eq (Z w a : ℕ) (hw : w ∣ q0 Z) (hw0 : 0 < w) :
    MajorArcs.inner Z w a = ((kap Z : ℝ) : ℂ) * ∑ r ∈ R0 Z, ee ((a : ℝ) * r / w) := by
  obtain ⟨k, hk⟩ := id hw
  have hkdiv : q0 Z / w = k := by rw [hk, Nat.mul_div_cancel_left _ hw0]
  have hq : ∀ ℓ, qell Z w a ℓ = q0 Z / Nat.gcd (q0 Z) (a * k + ℓ) := fun ℓ => by
    rw [qell_of_dvd a ℓ hw hw0, hkdiv]
  unfold MajorArcs.inner
  simp only [hq]
  have hswap : ∑ ℓ ∈ range (q0 Z), (muphi (q0 Z / Nat.gcd (q0 Z) (a * k + ℓ)) : ℂ) *
        ∑ r ∈ R0 Z, ee (-((ℓ : ℝ) * r / q0 Z)) =
      ∑ r ∈ R0 Z, ∑ ℓ ∈ range (q0 Z), (muphi (q0 Z / Nat.gcd (q0 Z) (a * k + ℓ)) : ℂ) *
        ee (-((ℓ : ℝ) * r / q0 Z)) := by
    simp_rw [mul_sum]; exact sum_comm
  rw [hswap, mul_sum]
  refine sum_congr rfl fun r hr => ?_
  have hrc : r.Coprime (q0 Z) := (mem_filter.mp hr).2.1
  have hterm : ∀ ℓ, (muphi (q0 Z / Nat.gcd (q0 Z) (a * k + ℓ)) : ℂ) *
      ee (-((ℓ : ℝ) * r / q0 Z)) =
      ee ((a : ℝ) * r / w) * ((muphi (q0 Z / Nat.gcd (q0 Z) ((a * k + ℓ) % q0 Z)) : ℂ) *
        ee ((((a * k + ℓ) % q0 Z : ℕ) : ℝ) * (((-(r : ℤ)) : ℤ) : ℝ) / q0 Z)) := by
    intro ℓ
    rw [gcd_mod]
    set b := (a * k + ℓ) % q0 Z
    set t := (a * k + ℓ) / q0 Z
    have e1 : b + q0 Z * t = a * k + ℓ := Nat.mod_add_div _ _
    have e1' : (ℓ : ℝ) = b + q0 Z * t - a * k := by
      have := congrArg (Nat.cast (R := ℝ)) e1; push_cast at this; linarith
    have hnR : (q0 Z : ℝ) = w * k := by rw [hk]; push_cast; ring
    have hw0' : (w : ℝ) ≠ 0 := by exact_mod_cast hw0.ne'
    have hk0 : (k : ℝ) ≠ 0 := by
      have : (q0 Z : ℝ) ≠ 0 := by exact_mod_cast (q0_pos Z).ne'
      intro h0; rw [hnR, h0, mul_zero] at this; exact this rfl
    have key : -((ℓ : ℝ) * r / q0 Z) = (a : ℝ) * r / w +
        ((b : ℝ) * (((-(r : ℤ)) : ℤ) : ℝ) / q0 Z + (((-((t * r : ℕ) : ℤ)) : ℤ) : ℝ)) := by
      rw [e1', hnR]; push_cast; field_simp; ring
    rw [key, ee_add, ee_add, ee_int, mul_one]
    ring
  rw [sum_congr rfl (fun ℓ _ => hterm ℓ), ← mul_sum]
  rw [sum_shift (q0 Z) (a * k) (q0_pos Z)
    (fun b => (muphi (q0 Z / Nat.gcd (q0 Z) b) : ℂ) *
      ee ((b : ℝ) * (((-(r : ℤ)) : ℤ) : ℝ) / q0 Z))]
  rw [← farey (q0 Z) (q0_pos Z) (fun d => (muphi d : ℂ)) (-(r : ℤ))]
  have hram : ∑ d ∈ (q0 Z).divisors, (muphi d : ℂ) *
      ∑ c ∈ U d, ee ((c : ℝ) * (((-(r : ℤ)) : ℤ) : ℝ) / d) =
      ∑ d ∈ (q0 Z).divisors, (muphi d : ℂ) * ram d r := by
    refine sum_congr rfl fun d _ => ?_
    unfold ram
    congr 1
    refine sum_congr rfl fun c _ => ?_
    congr 1; push_cast; ring
  rw [hram, Ksum Z r hrc]
  ring

/-! ### Steps 2 and 3: `f(w)` and `G(q_0)` -/

/-- `s_t = r₁ + r₂ + r₃ - m`. -/
def sT (m : ℕ) (t : ℕ × ℕ × ℕ) : ℤ := ((t.1 + t.2.1 + t.2.2 : ℕ) : ℤ) - m

theorem cube_sum (s : Finset ℕ) (X : ℕ → ℂ) :
    (∑ r ∈ s, X r) ^ 3 = ∑ t ∈ s ×ˢ s ×ˢ s, X t.1 * X t.2.1 * X t.2.2 := by
  rw [pow_three, sum_mul_sum, sum_mul_sum, sum_product]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_product]
  refine sum_congr rfl fun y _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun z _ => ?_
  ring

theorem fq_eq (Z m w : ℕ) (hw : w ∣ q0 Z) (hw0 : 0 < w) :
    fq Z m w = ((kap Z : ℝ) : ℂ) ^ 3 / (q0 Z : ℂ) ^ 3 *
      ∑ t ∈ R0 Z ×ˢ R0 Z ×ˢ R0 Z, ∑ a ∈ U w, ee ((a : ℝ) * (sT m t : ℝ) / w) := by
  have hper : ∀ a : ℕ, ee (-((a : ℝ) * m / w)) * MajorArcs.inner Z w a ^ 3 =
      ((kap Z : ℝ) : ℂ) ^ 3 *
        ∑ t ∈ R0 Z ×ˢ R0 Z ×ˢ R0 Z, ee ((a : ℝ) * (sT m t : ℝ) / w) := by
    intro a
    rw [inner_eq Z w a hw hw0, mul_pow, cube_sum]
    simp only [mul_sum]
    refine sum_congr rfl fun t _ => ?_
    have e : ee ((a : ℝ) * t.1 / w) * ee ((a : ℝ) * t.2.1 / w) * ee ((a : ℝ) * t.2.2 / w) *
        ee (-((a : ℝ) * m / w)) = ee ((a : ℝ) * (sT m t : ℝ) / w) := by
      unfold ee sT; simp only [← Complex.exp_add]; congr 1; push_cast; ring
    rw [← e]; ring
  unfold fq
  rw [sum_congr rfl (fun a _ => hper a), ← mul_sum, sum_comm]
  unfold U
  ring

theorem Gq0_eq_card (Z m : ℕ) : Gq0 Z m = ((kap Z : ℝ) : ℂ) ^ 3 / (q0 Z : ℂ) ^ 3 *
    ((q0 Z : ℂ) * (#((R0 Z ×ˢ R0 Z ×ˢ R0 Z).filter (fun t => (q0 Z : ℤ) ∣ sT m t)) : ℂ)) := by
  unfold Gq0
  rw [sum_congr rfl (fun w hw => fq_eq Z m w (Nat.dvd_of_mem_divisors hw)
    (Nat.pos_of_mem_divisors hw)), ← mul_sum, sum_comm (s := (q0 Z).divisors)]
  congr 1
  have h1 : ∀ t, ∑ w ∈ (q0 Z).divisors, ∑ a ∈ U w, ee ((a : ℝ) * (sT m t : ℝ) / w) =
      if (q0 Z : ℤ) ∣ sT m t then (q0 Z : ℂ) else 0 := by
    intro t
    have hf := farey (q0 Z) (q0_pos Z) (fun _ => (1 : ℂ)) (sT m t)
    simp only [one_mul] at hf
    rw [hf, sum_range_ee _ (q0_pos Z)]
  rw [sum_congr rfl (fun t _ => h1 t), ← sum_filter, sum_const, nsmul_eq_mul]
  ring

/-! ### Step 4: the CRT count of triples -/

theorem mod_mem_Lset_of_R0 {Z r p : ℕ} (hr : r ∈ R0 Z) (hp : p ∈ Nat.primesBelow Z) :
    r % p ∈ Lset p := by
  simp only [R0, mem_filter] at hr
  obtain ⟨s, hs, hrs⟩ := hr.2.2 p hp
  have h0 := mod_ne_zero_of_coprime (Nat.prime_of_mem_primesBelow hp) (dvd_q0 hp) hr.2.1
  unfold Lset; simp only [mem_filter, mem_image]
  exact ⟨⟨s, hs, hrs.symm⟩, h0⟩

theorem R0_eq_of_mod {Z r r' : ℕ} (hr : r ∈ R0 Z) (hr' : r' ∈ R0 Z)
    (h : ∀ p ∈ Nat.primesBelow Z, r % p = r' % p) : r = r' := by
  simp only [R0, mem_filter, mem_Icc] at hr hr'
  have hq := modEq_q0 (fun p hp => (h p hp : r ≡ r' [MOD p]))
  rcases le_total r r' with h' | h'
  · have hd := (Nat.modEq_iff_dvd' h').mp hq
    have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  · have hd := (Nat.modEq_iff_dvd' h').mp hq.symm
    have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega

/-- The local triples at `p`. -/
def Tp (p m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Lset p ×ˢ Lset p ×ˢ Lset p).filter (fun t => t.1 + t.2.1 + t.2.2 ≡ m [MOD p])

/-- **CRT**: `#{t ∈ R_0³ : r₁ + r₂ + r₃ ≡ m mod q_0} = ∏_{p < Z} N_p(m)`. -/
theorem card_triples (Z m : ℕ) :
    #((R0 Z ×ˢ R0 Z ×ˢ R0 Z).filter (fun t => t.1 + t.2.1 + t.2.2 ≡ m [MOD q0 Z])) =
      ∏ p ∈ Nat.primesBelow Z, Np p m := by
  have hNp : ∀ p, Np p m = #(Tp p m) := fun p => rfl
  simp only [hNp]
  rw [← card_pi]
  refine card_bij (fun t _ => fun p _ => (t.1 % p, t.2.1 % p, t.2.2 % p)) ?_ ?_ ?_
  · intro t ht
    simp only [mem_filter, mem_product] at ht
    obtain ⟨⟨h1, h2, h3⟩, hs⟩ := ht
    rw [Finset.mem_pi]
    intro p hp
    simp only [Tp, mem_filter, mem_product]
    refine ⟨⟨mod_mem_Lset_of_R0 h1 hp, mod_mem_Lset_of_R0 h2 hp, mod_mem_Lset_of_R0 h3 hp⟩, ?_⟩
    have hs' := hs.of_dvd (dvd_q0 hp)
    exact (((Nat.mod_modEq _ _).add (Nat.mod_modEq _ _)).add (Nat.mod_modEq _ _)).trans hs'
  · intro t ht t' ht' h
    simp only [mem_filter, mem_product] at ht ht'
    have hpe : ∀ p ∈ Nat.primesBelow Z,
        (t.1 % p, t.2.1 % p, t.2.2 % p) = (t'.1 % p, t'.2.1 % p, t'.2.2 % p) :=
      fun p hp => congrFun (congrFun h p) hp
    have e1 := R0_eq_of_mod ht.1.1 ht'.1.1 (fun p hp => (Prod.ext_iff.mp (hpe p hp)).1)
    have e2 := R0_eq_of_mod ht.1.2.1 ht'.1.2.1
      (fun p hp => (Prod.ext_iff.mp (Prod.ext_iff.mp (hpe p hp)).2).1)
    have e3 := R0_eq_of_mod ht.1.2.2 ht'.1.2.2
      (fun p hp => (Prod.ext_iff.mp (Prod.ext_iff.mp (hpe p hp)).2).2)
    exact Prod.ext e1 (Prod.ext e2 e3)
  · intro x hx
    rw [Finset.mem_pi] at hx
    let X : ℕ → ℕ × ℕ × ℕ := fun p => if hp : p ∈ Nat.primesBelow Z then x p hp else (0, 0, 0)
    have hX : ∀ p (hp : p ∈ Nat.primesBelow Z), X p = x p hp := fun p hp => by
      simp only [X, hp, dite_true]
    have hXT : ∀ p ∈ Nat.primesBelow Z, X p ∈ Tp p m := fun p hp => by
      rw [hX p hp]; exact hx p hp
    have hs : ∀ p ∈ Nat.primesBelow Z, id p ≠ 0 := fun p hp =>
      (Nat.prime_of_mem_primesBelow hp).ne_zero
    have pp : Set.Pairwise (↑(Nat.primesBelow Z) : Set ℕ) (Function.onFun Nat.Coprime id) :=
      fun p hp q hq hne => (Nat.coprime_primes (Nat.prime_of_mem_primesBelow hp)
        (Nat.prime_of_mem_primesBelow hq)).mpr hne
    have hL : ∀ p ∈ Nat.primesBelow Z, (X p).1 ∈ Lset p ∧ (X p).2.1 ∈ Lset p ∧
        (X p).2.2 ∈ Lset p ∧ (X p).1 + (X p).2.1 + (X p).2.2 ≡ m [MOD p] := by
      intro p hp
      have := hXT p hp
      simp only [Tp, mem_filter, mem_product] at this
      exact ⟨this.1.1, this.1.2.1, this.1.2.2, this.2⟩
    let k₁ := Nat.chineseRemainderOfFinset (fun p => (X p).1) id (Nat.primesBelow Z) hs pp
    let k₂ := Nat.chineseRemainderOfFinset (fun p => (X p).2.1) id (Nat.primesBelow Z) hs pp
    let k₃ := Nat.chineseRemainderOfFinset (fun p => (X p).2.2) id (Nat.primesBelow Z) hs pp
    have m1 := rep_mem_R0 Z k₁ (fun p => (X p).1) (fun p hp => (hL p hp).1) k₁.2
    have m2 := rep_mem_R0 Z k₂ (fun p => (X p).2.1) (fun p hp => (hL p hp).2.1) k₂.2
    have m3 := rep_mem_R0 Z k₃ (fun p => (X p).2.2) (fun p hp => (hL p hp).2.2.1) k₃.2
    have c1 : ∀ p ∈ Nat.primesBelow Z, rep Z k₁ ≡ (X p).1 [MOD p] := fun p hp =>
      ((rep_modEq Z k₁).of_dvd (dvd_q0 hp)).trans (k₁.2 p hp)
    have c2 : ∀ p ∈ Nat.primesBelow Z, rep Z k₂ ≡ (X p).2.1 [MOD p] := fun p hp =>
      ((rep_modEq Z k₂).of_dvd (dvd_q0 hp)).trans (k₂.2 p hp)
    have c3 : ∀ p ∈ Nat.primesBelow Z, rep Z k₃ ≡ (X p).2.2 [MOD p] := fun p hp =>
      ((rep_modEq Z k₃).of_dvd (dvd_q0 hp)).trans (k₃.2 p hp)
    have lt : ∀ p ∈ Nat.primesBelow Z, ∀ y ∈ Lset p, y % p = y := fun p hp y hy => by
      have := Lset_sub p (Nat.prime_of_mem_primesBelow hp).pos hy
      exact Nat.mod_eq_of_lt (mem_Ico.mp this).2
    refine ⟨(rep Z k₁, rep Z k₂, rep Z k₃), ?_, ?_⟩
    · simp only [mem_filter, mem_product]
      refine ⟨⟨m1, m2, m3⟩, modEq_q0 fun p hp => ?_⟩
      exact (((c1 p hp).add (c2 p hp)).add (c3 p hp)).trans (hL p hp).2.2.2
    · funext p hp
      rw [← hX p hp]
      have r1 : rep Z k₁ % p = (X p).1 := by
        rw [c1 p hp]; exact lt p hp _ (hL p hp).1
      have r2 : rep Z k₂ % p = (X p).2.1 := by
        rw [c2 p hp]; exact lt p hp _ (hL p hp).2.1
      have r3 : rep Z k₃ % p = (X p).2.2 := by
        rw [c3 p hp]; exact lt p hp _ (hL p hp).2.2.1
      simp only [r1, r2, r3]

/-! ### Step 5: Lemma 8.2 -/

/-- **Lemma 8.2 with the local evaluation, PROVED**: `G(q_0) = ∏_{p < Z} p N_p(m)/(p-1)³`
for every `Z` and every `m`. -/
theorem lemma82_eq (Z m : ℕ) : Gq0 Z m = (Gprod Z m : ℂ) := by
  have hfilt : (R0 Z ×ˢ R0 Z ×ˢ R0 Z).filter (fun t => (q0 Z : ℤ) ∣ sT m t) =
      (R0 Z ×ˢ R0 Z ×ˢ R0 Z).filter (fun t => t.1 + t.2.1 + t.2.2 ≡ m [MOD q0 Z]) := by
    refine filter_congr fun t _ => ?_
    unfold sT
    rw [Nat.ModEq.comm, Nat.modEq_iff_dvd]
  rw [Gq0_eq_card, hfilt, card_triples]
  have key : (kap Z) ^ 3 / (q0 Z : ℝ) ^ 2 * (∏ p ∈ Nat.primesBelow Z, (Np p m : ℝ)) =
      Gprod Z m := by
    unfold kap Gprod q0
    push_cast
    rw [← prod_pow, ← prod_pow, ← prod_div_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have h1 : (p : ℝ) - 1 ≠ 0 := by intro h; linarith
    have h0 : (p : ℝ) ≠ 0 := by intro h; linarith
    field_simp
  rw [← key]
  have hq : (q0 Z : ℂ) ≠ 0 := by exact_mod_cast (q0_pos Z).ne'
  push_cast
  field_simp

/-- **`Lemma82` PROVED.** -/
theorem lemma82 : Lemma82 := fun Z m _ => lemma82_eq Z m

/-- **MajorLower, CONDITIONAL ON `Major618 A B` and `Tail72 A B`** only. -/
theorem majorLower_of_analytic (A B : ℕ) (hA : 1 ≤ A) (hB : 36 * A + 3 ≤ B)
    (h618 : Major618 A B) (h72 : Tail72 A B) : MajorLower A B (9 * (A : ℝ) + 1) :=
  majorLower_of_three A B hA hB h618 h72 lemma82

/-- **RepProp A, CONDITIONAL ON `Minor516W A B`, `Major618 A B`, `Tail72 A B`** only. -/
theorem repProp_of_analytic (A B : ℕ) (hA : 1 ≤ A) (hB1 : 36 * A + 3 ≤ B)
    (hB2 : 28 * A + 13 ≤ B) (hmin : RepAssembly.Minor516W A B) (h618 : Major618 A B)
    (h72 : Tail72 A B) : RepProp A :=
  repProp_of_inputs A B hA hB1 hB2 hmin h618 h72 lemma82 euler716

/-! ### Vacuity tests -/

/-- `lemma82_eq` at `Z = 4`, `q_0 = 6`, `m = 1`: a genuine instance with two primes. -/
example : Gq0 4 1 = (Gprod 4 1 : ℂ) := lemma82_eq 4 1

/-- At `Z = 4`, `m = 1`, `G(q_0)` is real and at least `1/36`, from `G_lower`. -/
example : ∃ x : ℝ, Gq0 4 1 = (x : ℂ) ∧ 1 / 36 ≤ x := by
  refine ⟨Gprod 4 1, lemma82_eq 4 1, ?_⟩
  have h := G_lower 4 1 odd_one
  have hq : q0 4 = 6 := by decide
  rw [hq] at h; norm_num at h ⊢; linarith

/-- `sum_range_ee` at `n = 3`, `s = 1`: the cube roots of unity sum to `0`. -/
example : ∑ b ∈ range 3, ee ((b : ℝ) * ((1 : ℤ) : ℝ) / ((3 : ℕ) : ℝ)) = 0 := by
  rw [sum_range_ee 3 (by norm_num) 1]; norm_num

/-- The side conditions of `repProp_of_analytic` hold at `A = 1`, `B = 41`. -/
example : 1 ≤ (1 : ℕ) ∧ 36 * 1 + 3 ≤ (41 : ℕ) ∧ 28 * 1 + 13 ≤ (41 : ℕ) := by norm_num

end LeanLab.SparseTernary.Lemma82Proof

#print axioms LeanLab.SparseTernary.Lemma82Proof.farey
#print axioms LeanLab.SparseTernary.Lemma82Proof.Ksum
#print axioms LeanLab.SparseTernary.Lemma82Proof.inner_eq
#print axioms LeanLab.SparseTernary.Lemma82Proof.card_triples
#print axioms LeanLab.SparseTernary.Lemma82Proof.lemma82_eq
#print axioms LeanLab.SparseTernary.Lemma82Proof.lemma82
#print axioms LeanLab.SparseTernary.Lemma82Proof.majorLower_of_analytic
#print axioms LeanLab.SparseTernary.Lemma82Proof.repProp_of_analytic

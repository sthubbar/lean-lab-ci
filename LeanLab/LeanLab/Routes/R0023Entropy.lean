/-
# R-0023, T3 MOONSHOT: Tao's entropy decrement and the reflected Liouville pair

Unit U-1190, PC run 20261020T0703Z-22071.

Tao 2016 proved the logarithmically averaged two-point Chowla conjecture. Its engine is the
identity `λ(pn)λ(pn + ph) = λ(n)λ(n + h)`: a correlation at shift `h` is the part on multiples
of `p` of a correlation at shift `ph`, and the entropy decrement removes the condition `p ∣ n`
on average over `p`. For the reflected pair of binary Goldbach, `c(N) = Σ_{a+b=N} λ(a)λ(b)`,
the same identity reads `λ(pa)λ(p(N − a)) = λ(a)λ(N − a)`, so dilation moves the TARGET `N` to
`pN` and never averages over anything at a fixed `N`.

PROVED here, unconditional:
* `liouville_prime`: `λ(p) = −1`.
* `liouville_dil`: `λ(pa)λ(pb) = λ(a)λ(b)` for prime `p`.
* `cMult_eq`: the multiples-of-`p` part of `c(pN)` is exactly `c(N)`.
* `c_eq_dil_sub`: `c(N) = c(pN) − cRest p N`, the rest being the terms with `p ∤ a`.
* `cLogMult_eq`: with Tao's logarithmic weight `1/a`, the multiples part of `c_log(pN)` is
  exactly `c_log(N)/p`, the `1/p` that Tao's averaging over `p` uses.
KNOWN mathematics, elementary. AI wrote this Lean code. Binary Goldbach is OPEN; this route is
not progress on it.
-/
import Mathlib

namespace LeanLab.Routes.R0023

open Finset ArithmeticFunction

/-- `λ(p) = −1` for a prime `p`. -/
theorem liouville_prime {p : ℕ} (hp : p.Prime) : liouville p = -1 := by
  rw [liouville_apply hp.ne_zero, cardFactors_apply_prime hp, pow_one]

/-- The dilation identity: `λ(pa)λ(pb) = λ(a)λ(b)`. -/
theorem liouville_dil {p : ℕ} (hp : p.Prime) (a b : ℕ) :
    liouville (p * a) * liouville (p * b) = liouville a * liouville b := by
  rw [liouville_apply_mul, liouville_apply_mul, liouville_prime hp]
  ring

/-- The reflected Liouville correlation `c(N) = Σ_{a+b=N} λ(a)λ(b)`; the ends vanish, `λ(0) = 0`. -/
def c (N : ℕ) : ℤ := ∑ a ∈ range (N + 1), liouville a * liouville (N - a)

/-- The part of `c(pN)` on multiples of `p`. -/
def cMult (p N : ℕ) : ℤ :=
  ∑ a ∈ (range (p * N + 1)).filter (fun a => p ∣ a), liouville a * liouville (p * N - a)

/-- The rest of `c(pN)`, the terms with `p ∤ a`. -/
def cRest (p N : ℕ) : ℤ :=
  ∑ a ∈ (range (p * N + 1)).filter (fun a => ¬ p ∣ a), liouville a * liouville (p * N - a)

theorem filter_dvd_eq_image {p N : ℕ} (hp : 0 < p) :
    (range (p * N + 1)).filter (fun a => p ∣ a) = (range (N + 1)).image (fun b => p * b) := by
  ext a
  simp only [mem_filter, mem_range, mem_image]
  constructor
  · rintro ⟨ha, b, rfl⟩
    refine ⟨b, ?_, rfl⟩
    by_contra h
    push_neg at h
    have : p * (N + 1) ≤ p * b := Nat.mul_le_mul_left p h
    nlinarith
  · rintro ⟨b, hb, rfl⟩
    refine ⟨?_, dvd_mul_right p b⟩
    have : p * b ≤ p * N := Nat.mul_le_mul_left p (by omega)
    omega

/-- The multiples-of-`p` part of `c(pN)` is exactly `c(N)`. -/
theorem cMult_eq {p : ℕ} (hp : p.Prime) (N : ℕ) : cMult p N = c N := by
  unfold cMult c
  rw [filter_dvd_eq_image hp.pos, sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hp.pos h)]
  apply sum_congr rfl
  intro b _
  rw [← Nat.mul_sub, liouville_dil hp]

/-- `c(N) = c(pN) − cRest p N`: a fixed `N` is read off a dilate only through the rest. -/
theorem c_eq_dil_sub {p : ℕ} (hp : p.Prime) (N : ℕ) : c N = c (p * N) - cRest p N := by
  have h := sum_filter_add_sum_filter_not (range (p * N + 1)) (fun a => p ∣ a)
    (fun a => liouville a * liouville (p * N - a))
  rw [← cMult_eq hp N]
  unfold c cMult cRest
  linarith

/-- Tao's logarithmic weight: `c_log(N) = Σ_{a+b=N} λ(a)λ(b)/a`, `a ≥ 1`. -/
noncomputable def cLog (N : ℕ) : ℚ :=
  ∑ a ∈ range (N + 1), (liouville a * liouville (N - a) : ℚ) / a

noncomputable def cLogMult (p N : ℕ) : ℚ :=
  ∑ a ∈ (range (p * N + 1)).filter (fun a => p ∣ a),
    (liouville a * liouville (p * N - a) : ℚ) / a

/-- With the weight `1/a`, the multiples part of `c_log(pN)` is `c_log(N)/p`. -/
theorem cLogMult_eq {p : ℕ} (hp : p.Prime) (N : ℕ) : cLogMult p N = cLog N / p := by
  unfold cLogMult cLog
  rw [filter_dvd_eq_image hp.pos, sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hp.pos h),
    sum_div]
  apply sum_congr rfl
  intro b _
  rw [← Nat.mul_sub]
  have h := liouville_dil hp b (N - b)
  have hq : ((liouville (p * b) : ℚ) * (liouville (p * (N - b)) : ℚ))
      = (liouville b : ℚ) * (liouville (N - b) : ℚ) := by exact_mod_cast h
  rw [hq]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  push_cast
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp
  · have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    field_simp

/-- Vacuity: `c(4) = λ(1)λ(3) + λ(2)λ(2) + λ(3)λ(1) = −1 + 1 − 1 = −1`. -/
example : c 4 = -1 := by
  have h1 : liouville 1 = 1 := liouville_apply_one
  have h2 : liouville 2 = -1 := liouville_prime Nat.prime_two
  have h3 : liouville 3 = -1 := liouville_prime Nat.prime_three
  have h0 : liouville 0 = 0 := liouville.map_zero
  have h4 : liouville 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, liouville_apply_mul, h2]; norm_num
  unfold c
  rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ,
    sum_range_zero]
  norm_num [h0, h1, h2, h3, h4]

end LeanLab.Routes.R0023

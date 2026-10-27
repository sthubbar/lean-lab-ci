/-
R-5270, CLOUD 20261020T2018Z-cloud50, unit U-6728, T3 MOONSHOT.
AI wrote this Lean code. Not progress on binary Goldbach, which is OPEN.

The Goldbach resultant.  For a finite set A of naturals and a target N,
  res A N = ∏_{a ∈ A} ∏_{b ∈ A} (N - a - b)   in ℤ,
the resultant of F(x) = ∏ (x - a) and F(N - x) up to sign.
* `res_eq_zero_iff`: res A N = 0 iff N = a + b with a, b ∈ A.
* `prime_dvd_res_iff`: a prime ℓ divides res A N iff N ∈ A + A mod ℓ.
* `dvd_res_of_pigeonhole`: if A meets more than ℓ/2 classes mod ℓ, then ℓ
  divides res A N for every N; this is the free local data, the polynomial
  method and Cauchy-Davenport live here.
* `natAbs_res_le`: |res A N| ≤ N ^ (|A|²) for A ⊆ [0, N].
* `crt_certificate`: a divisor M of res A N with M > N ^ (|A|²) forces a
  representation; the only way local data could prove Goldbach.
* `large_prime_dvd_iff`: for a prime ℓ > N, ℓ ∣ res A N iff N ∈ A + A, so
  large moduli are circular.
* `small_primes_too_small`: if 4 ≤ N ≤ |A|², no product of primes ≤ N exceeds
  N ^ (|A|²), so the certificate can never be made of small primes.
-/
import Mathlib

namespace LeanLab.Routes.R5270

open Finset

/-- The Goldbach resultant of A at N. -/
def res (A : Finset ℕ) (N : ℕ) : ℤ :=
  ∏ a ∈ A, ∏ b ∈ A, ((N : ℤ) - a - b)

theorem res_eq_zero_iff (A : Finset ℕ) (N : ℕ) :
    res A N = 0 ↔ ∃ a ∈ A, ∃ b ∈ A, a + b = N := by
  unfold res
  simp only [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨a, ha, b, hb, by omega⟩
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨a, ha, b, hb, by omega⟩

theorem prime_dvd_res_iff (A : Finset ℕ) (N ℓ : ℕ) (hℓ : ℓ.Prime) :
    (ℓ : ℤ) ∣ res A N ↔ ∃ a ∈ A, ∃ b ∈ A, (ℓ : ℤ) ∣ ((N : ℤ) - a - b) := by
  have hp : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  unfold res
  rw [Prime.dvd_finsetProd_iff hp]
  simp only [Prime.dvd_finsetProd_iff hp]

/-- Pigeonhole in ZMod ℓ: more than ℓ/2 classes give every target. -/
theorem dvd_res_of_pigeonhole (A : Finset ℕ) (N ℓ : ℕ) (hℓ : ℓ.Prime)
    (hcard : ℓ < 2 * (A.image (fun a : ℕ => (a : ZMod ℓ))).card) :
    (ℓ : ℤ) ∣ res A N := by
  classical
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  set S := A.image (fun a : ℕ => (a : ZMod ℓ)) with hS
  set T := S.image (fun s : ZMod ℓ => (N : ZMod ℓ) - s) with hT
  have hTc : T.card = S.card := by
    apply Finset.card_image_of_injective
    intro x y h
    simpa using h
  have hdisj : ¬ Disjoint S T := by
    intro hd
    have h1 := Finset.card_union_of_disjoint hd
    have h2 : (S ∪ T).card ≤ ℓ := by
      calc (S ∪ T).card ≤ (Finset.univ : Finset (ZMod ℓ)).card :=
            Finset.card_le_univ _
        _ = ℓ := by simp [ZMod.card]
    omega
  rw [Finset.not_disjoint_iff] at hdisj
  obtain ⟨x, hxS, hxT⟩ := hdisj
  rw [hT, Finset.mem_image] at hxT
  obtain ⟨s, hsS, hsx⟩ := hxT
  rw [hS, Finset.mem_image] at hxS hsS
  obtain ⟨a, ha, rfl⟩ := hxS
  obtain ⟨b, hb, rfl⟩ := hsS
  rw [prime_dvd_res_iff A N ℓ hℓ]
  refine ⟨a, ha, b, hb, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [← hsx]
  ring

private lemma natAbs_prod' {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∏ i ∈ s, f i).natAbs = ∏ i ∈ s, (f i).natAbs :=
  map_prod Int.natAbsHom f s

theorem natAbs_res_le (A : Finset ℕ) (N : ℕ) (hA : ∀ a ∈ A, a ≤ N) :
    (res A N).natAbs ≤ N ^ (A.card ^ 2) := by
  unfold res
  rw [natAbs_prod']
  have h : ∀ a ∈ A, (∏ b ∈ A, ((N : ℤ) - a - b)).natAbs ≤ N ^ A.card := by
    intro a ha
    rw [natAbs_prod']
    apply Finset.prod_le_pow_card
    intro b hb
    have := hA a ha
    have := hA b hb
    omega
  calc (∏ a ∈ A, (∏ b ∈ A, ((N : ℤ) - a - b)).natAbs)
      ≤ (N ^ A.card) ^ A.card := Finset.prod_le_pow_card _ _ _ h
    _ = N ^ (A.card ^ 2) := by rw [← pow_mul, sq]

/-- The CRT certificate: a large enough divisor forces a representation. -/
theorem crt_certificate (A : Finset ℕ) (N M : ℕ) (hA : ∀ a ∈ A, a ≤ N)
    (hM : (M : ℤ) ∣ res A N) (hbig : N ^ (A.card ^ 2) < M) :
    ∃ a ∈ A, ∃ b ∈ A, a + b = N := by
  rw [← res_eq_zero_iff]
  by_contra h0
  have h1 : M ≤ (res A N).natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hM
    simp only [Int.natAbs_natCast] at this
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr h0) this
  have := natAbs_res_le A N hA
  omega

/-- A prime above N divides the resultant only when N is already represented. -/
theorem large_prime_dvd_iff (A : Finset ℕ) (N ℓ : ℕ) (hℓ : ℓ.Prime)
    (hA : ∀ a ∈ A, a ≤ N) (hN : N < ℓ) :
    (ℓ : ℤ) ∣ res A N ↔ ∃ a ∈ A, ∃ b ∈ A, a + b = N := by
  rw [prime_dvd_res_iff A N ℓ hℓ]
  constructor
  · rintro ⟨a, ha, b, hb, hd⟩
    refine ⟨a, ha, b, hb, ?_⟩
    have h1 := hA a ha
    have h2 := hA b hb
    have hx : ((N : ℤ) - a - b) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd hd
      rw [abs_lt]; constructor <;> omega
    omega
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨a, ha, b, hb, by rw [show ((N : ℤ) - a - b) = 0 by omega]; simp⟩

/-- Small primes cannot certify: if 4 ≤ N ≤ |A|², every divisor of the
primorial N# is at most N ^ (|A|²). -/
theorem small_primes_too_small (A : Finset ℕ) (N M : ℕ) (hN : 4 ≤ N)
    (hA : N ≤ A.card ^ 2) (hM : M ∣ primorial N) :
    M ≤ N ^ (A.card ^ 2) := by
  have h1 : M ≤ primorial N := Nat.le_of_dvd (primorial_pos N) hM
  have h2 := primorial_le_four_pow N
  have h3 : 4 ^ N ≤ 4 ^ (A.card ^ 2) := Nat.pow_le_pow_right (by norm_num) hA
  have h4 : 4 ^ (A.card ^ 2) ≤ N ^ (A.card ^ 2) := Nat.pow_le_pow_left hN _
  omega

/-- Vacuity: the hypotheses of `small_primes_too_small` hold at N = 10 with
A the primes up to 10, and the resultant there is 0, since 10 = 3 + 7. -/
example : 4 ≤ 10 ∧ 10 ≤ ({2, 3, 5, 7} : Finset ℕ).card ^ 2 ∧
    res {2, 3, 5, 7} 10 = 0 := by
  refine ⟨by norm_num, by decide, ?_⟩
  rw [res_eq_zero_iff]
  exact ⟨3, by decide, 7, by decide, rfl⟩

/-- Vacuity for the fake side: A = {3, 5} has no representation of 9 but
3 ∣ res A 9, by pigeonhole data alone. -/
example : res {3, 5} 9 ≠ 0 ∧ (3 : ℤ) ∣ res {3, 5} 9 := by
  refine ⟨by decide, by decide⟩

end LeanLab.Routes.R5270

#print axioms LeanLab.Routes.R5270.res_eq_zero_iff
#print axioms LeanLab.Routes.R5270.prime_dvd_res_iff
#print axioms LeanLab.Routes.R5270.dvd_res_of_pigeonhole
#print axioms LeanLab.Routes.R5270.natAbs_res_le
#print axioms LeanLab.Routes.R5270.crt_certificate
#print axioms LeanLab.Routes.R5270.large_prime_dvd_iff
#print axioms LeanLab.Routes.R5270.small_primes_too_small

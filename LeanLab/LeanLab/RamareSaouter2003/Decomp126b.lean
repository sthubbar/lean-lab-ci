import Mathlib

/-!
P0099, Lemma 8 and its written proof on p. 27.
The factorization parameters are positive natural numbers.
The congruence base is an integer, as in the paper.
AI wrote this Lean code. Binary Goldbach is OPEN.
The assembly remains CONDITIONAL ON the external Pocklington leaf.
-/

namespace LeanLab.RamareSaouter2003.Decomp126b

/-- CITED. Lemma 8, p. 27. The complete known factorization of the positive
even F is represented by the condition for every prime divisor of F. -/
def lemma8_stmt : Prop := ∀ N R F s r : ℕ,
    2 ≤ N → 2 ≤ F → Even F → Nat.Coprime R F → Odd N →
    N = R * F + 1 → R = 2 * F * s + r → r < 2 * F → N < 2 * F ^ 3 →
    (∃ a : ℤ, Int.ModEq (N : ℤ) (a ^ (N - 1)) 1 ∧
      ∀ p : ℕ, p.Prime → p ∣ F → Int.gcd (a ^ ((N - 1) / p) - 1) N = 1) →
    (N.Prime ↔ s = 0 ∨ ¬ IsSquare ((r : ℤ) ^ 2 - 8 * s))

/-- LEAF. The coprimality and evenness assumptions make R odd.
Lemma 8, p. 27, the parity needed in identifying the two factors. -/
theorem odd_R {R F : ℕ} (hcop : Nat.Coprime R F) (hF : Even F) : Odd R := by
  have h2 : 2 ∣ F := even_iff_two_dvd.mp hF
  have hc : Nat.Coprime R 2 := hcop.of_dvd_right h2
  exact Nat.Coprime.odd_of_right hc

/-- The exponent of a prime `p` in a factorization of `M` divides any divisor
`m` of `M` that does not divide `M / p`. -/

private theorem pow_factorization_dvd_of_not_dvd {M m p : ℕ} (hp : p.Prime)
    (hM0 : 0 < M) (hm0 : 0 < m) (hmm : m ∣ M) (hnd : ¬ m ∣ M / p) :
    p ^ (M.factorization p) ∣ m := by
  by_cases hpM : p ∣ M
  · obtain ⟨t, w, hpw, hM⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM0.ne' p hp.ne_one
    have ht1 : 1 ≤ t := by
      by_contra hc
      have ht0 : t = 0 := by omega
      have hMw : M = w := by rw [hM, ht0, pow_zero]; ring
      rw [hMw] at hpM
      exact hpw hpM
    have hMp : M / p = p ^ (t - 1) * w := by
      have hpt : p ^ t = p * p ^ (t - 1) := by
        rw [← Nat.pow_succ']
        congr 1
        omega
      rw [hM, hpt, Nat.mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    obtain ⟨j, u, hpu, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0.ne' p hp.ne_one
    have htj : t ≤ j := by
      by_contra hjt
      have hjle : j ≤ t - 1 := by omega
      have hcop : Nat.Coprime u p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpu).symm
      have huw : u ∣ w := by
        have hu_m : u ∣ m := by rw [hm]; exact Nat.dvd_mul_left u (p ^ j)
        have hu_M : u ∣ M := hu_m.trans hmm
        rw [hM] at hu_M
        exact (Nat.Coprime.pow_right t hcop).dvd_mul_left.mp hu_M
      have hdvd2 : m ∣ p ^ (t - 1) * w := by
        rw [hm]
        exact Nat.mul_dvd_mul (pow_dvd_pow p hjle) huw
      rw [hMp] at hnd
      exact hnd hdvd2
    have hpw' : ¬ p ^ (t + 1) ∣ M := by
      intro hd
      have hdM : p ^ (t + 1) ∣ p ^ t * w := by rwa [hM] at hd
      have hpm : p ^ t * p ∣ p ^ t * w := by rwa [Nat.pow_succ] at hdM
      exact hpw ((Nat.mul_dvd_mul_iff_left (Nat.pow_pos hp.pos)).mp hpm)
    have htfac : M.factorization p = t := by
      have h1 : t ≤ M.factorization p :=
        (Nat.Prime.pow_dvd_iff_le_factorization hp hM0.ne').mp ⟨w, hM⟩
      have h2 : ¬ t + 1 ≤ M.factorization p := fun hc =>
        hpw' ((Nat.Prime.pow_dvd_iff_le_factorization hp hM0.ne').mpr hc)
      omega
    rw [htfac]
    exact dvd_trans (pow_dvd_pow p htj) ⟨u, hm⟩
  · have hzero : M.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpM
    rw [hzero, pow_zero]
    exact one_dvd m

/-- Brillhart–Lehmer–Selfridge: every prime divisor of `N` is one modulo `F`,
the part of `N - 1` that the Fermat congruence certifies. -/

private theorem prime_dvd_mod_F {N R F : ℕ} (hN2 : 2 ≤ N) (hF2 : 2 ≤ F)
    (hN : N = R * F + 1) {a : ℤ} (ha : Int.ModEq (N : ℤ) (a ^ (N - 1)) 1)
    (hgcd : ∀ p : ℕ, p.Prime → p ∣ F → Int.gcd (a ^ ((N - 1) / p) - 1) N = 1)
    {q : ℕ} (hq : q.Prime) (hqN : q ∣ N) : F ∣ q - 1 := by
  have hF0 : 0 < F := by omega
  have hq1 : 1 < q := hq.one_lt
  have hM0 : 0 < N - 1 := by omega
  have hMs : N - 1 = R * F := by omega
  have hMF : F ∣ N - 1 := by rw [hMs]; exact ⟨R, mul_comm R F⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq.ne_one
  have hx1 : ((a : ZMod q)) ^ (N - 1) = 1 := by
    have h1 : ((N : ℤ) ∣ a ^ (N - 1) - 1) := ha.symm.dvd
    have h2 : ((q : ℤ) ∣ a ^ (N - 1) - 1) :=
      dvd_trans (Int.natCast_dvd_natCast.mpr hqN) h1
    have h3 : (((a : ℤ) ^ (N - 1) - 1 : ℤ) : ZMod q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2
    push_cast at h3
    exact eq_of_sub_eq_zero h3
  have hx0 : (a : ZMod q) ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM0.ne'] at hx1
    exact zero_ne_one hx1
  have hmord : 0 < orderOf (a : ZMod q) :=
    IsOfFinOrder.orderOf_pos (isOfFinOrder_iff_pow_eq_one.mpr ⟨N - 1, hM0, hx1⟩)
  have hmmN : orderOf (a : ZMod q) ∣ N - 1 := orderOf_dvd_of_pow_eq_one hx1
  have hmq : orderOf (a : ZMod q) ∣ q - 1 := ZMod.orderOf_dvd_card_sub_one hx0
  have hcore : ∀ p : ℕ, p.Prime → p ∣ F → p ^ ((N - 1).factorization p) ∣ q - 1 := by
    intro p hp hpf
    have hne : ((a : ZMod q) ^ ((N - 1) / p)) ≠ 1 := by
      intro hc
      have hg : Int.gcd (a ^ ((N - 1) / p) - 1) N = 1 := hgcd p hp hpf
      have h3 : (((a : ℤ) ^ ((N - 1) / p) - 1 : ℤ) : ZMod q) = 0 := by
        push_cast
        rw [hc, sub_self]
      have h2 : ((q : ℤ) ∣ a ^ ((N - 1) / p) - 1) :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h3
      have hqN' : ((q : ℤ) ∣ (N : ℤ)) := Int.natCast_dvd_natCast.mpr hqN
      have hqX : q ∣ (a ^ ((N - 1) / p) - 1).natAbs := Int.natCast_dvd.mp h2
      have hqNnat : q ∣ (N : ℤ).natAbs := Int.natCast_dvd.mp hqN'
      rw [Int.natAbs_natCast] at hqNnat
      have hg2 : (a ^ ((N - 1) / p) - 1).gcd (N : ℤ) = 1 := hgcd p hp hpf
      rw [Int.gcd_def, Int.natAbs_natCast] at hg2
      have hqgcd : q ∣ Nat.gcd (a ^ ((N - 1) / p) - 1).natAbs N :=
        Nat.dvd_gcd hqX hqNnat
      rw [hg2] at hqgcd
      exact hq.ne_one (Nat.dvd_one.mp hqgcd)
    have hnd : ¬ orderOf (a : ZMod q) ∣ (N - 1) / p := by
      intro hd
      exact hne ((orderOf_dvd_iff_pow_eq_one (x := (a : ZMod q))).mp hd)
    exact dvd_trans
      (pow_factorization_dvd_of_not_dvd hp hM0 hmord hmmN hnd) hmq
  refine (Nat.factorization_le_iff_dvd hF0.ne' (by omega : (q - 1) ≠ 0)).mp ?_
  rw [Finsupp.le_def]
  intro p
  by_cases pp : p.Prime
  · by_cases h0 : F.factorization p = 0
    · omega
    · have hpf : p ∣ F := Nat.dvd_of_factorization_pos h0
      have hpF : p ^ (F.factorization p) ∣ F :=
        (Nat.Prime.pow_dvd_iff_le_factorization pp hF0.ne').mpr (le_refl _)
      have h1 : F.factorization p ≤ (N - 1).factorization p :=
        (Nat.Prime.pow_dvd_iff_le_factorization pp hM0.ne').mp (dvd_trans hpF hMF)
      have h2 : (N - 1).factorization p ≤ (q - 1).factorization p :=
        (Nat.Prime.pow_dvd_iff_le_factorization pp (by omega)).mp (hcore p pp hpf)
      omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ pp,
      Nat.factorization_eq_zero_of_not_prime _ pp]

/-- A divisor of `N` larger than one is one modulo `F` as soon as every prime
divisor of `N` is: products of numbers one modulo `F` stay one modulo `F`. -/

private theorem divisors_mod_F {F N : ℕ} (hF0 : 0 < F)
    (hprime : ∀ q : ℕ, q.Prime → q ∣ N → ∃ k : ℕ, 0 < k ∧ q = k * F + 1) :
    ∀ d : ℕ, d ∣ N → 1 < d → ∃ k : ℕ, 0 < k ∧ d = k * F + 1 := by
  intro d
  refine Nat.strongRecOn d (fun d ih hdvdN hd1 => ?_)
  by_cases hdp : d.Prime
  · exact hprime d hdp hdvdN
  · obtain ⟨e, f, hde, hdf, hef⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega)).mp hdp
    have he1 : 1 < e := by
      by_contra hc
      rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
      · simp at hef; omega
      · simp at hef; omega
    have hf1 : 1 < f := by
      by_contra hc
      rcases (show f = 0 ∨ f = 1 by omega) with rfl | rfl
      · simp at hef; omega
      · simp at hef; omega
    have hed : e ∣ d := ⟨f, hef.symm⟩
    have hfd : f ∣ d := ⟨e, by rw [← hef]; ring⟩
    obtain ⟨k, hk0, hk⟩ := ih e hde (hed.trans hdvdN) he1
    obtain ⟨m, hm0, hm⟩ := ih f hdf (hfd.trans hdvdN) hf1
    refine ⟨k * m * F + k + m, by positivity, ?_⟩
    rw [← hef, hk, hm]
    ring

/-- LEAF. The Pocklington divisor property used in the first sentence of the
proof of Lemma 8 on p. 27. External source: Brillhart, Lehmer and Selfridge,
New primality criteria and factorizations of 2^m plus or minus 1, reference 6.
Every divisor greater than one is one modulo F. -/
theorem pocklington_divisors {N R F : ℕ} (hN2 : 2 ≤ N) (hF2 : 2 ≤ F)
    (hN : N = R * F + 1) {a : ℤ} (ha : Int.ModEq (N : ℤ) (a ^ (N - 1)) 1)
    (hgcd : ∀ p : ℕ, p.Prime → p ∣ F → Int.gcd (a ^ ((N - 1) / p) - 1) N = 1) :
    ∀ d : ℕ, d ∣ N → 1 < d → ∃ k : ℕ, 0 < k ∧ d = k * F + 1 := by
  intro d hdvdN hd1
  have hF0 : 0 < F := by omega
  have hprime : ∀ q : ℕ, q.Prime → q ∣ N → ∃ k : ℕ, 0 < k ∧ q = k * F + 1 := by
    intro q hq hqN
    have hq1 : 1 < q := hq.one_lt
    have hFq : F ∣ q - 1 := prime_dvd_mod_F hN2 hF2 hN ha hgcd hq hqN
    have hq10 : 0 < q - 1 := by omega
    have hFle : F ≤ q - 1 := Nat.le_of_dvd hq10 hFq
    refine ⟨(q - 1) / F, Nat.div_pos hFle hF0, ?_⟩
    have hmul : (q - 1) / F * F = q - 1 := by
      rw [mul_comm]
      exact Nat.mul_div_cancel' hFq
    omega
  exact divisors_mod_F hF0 hprime d hdvdN hd1

/-- LEAF. A composite N with the Pocklington divisor property has a grouping
into two factors giving r = u + v and 2s = uv. The size and parity argument
is the middle of the written proof of Lemma 8, p. 27. -/
theorem composite_roots {N R F s r : ℕ} (hN2 : 2 ≤ N) (hF2 : 2 ≤ F)
    (hF : Even F) (hRodd : Odd R) (hN : N = R * F + 1)
    (hR : R = 2 * F * s + r) (hr : r < 2 * F) (hbound : N < 2 * F ^ 3)
    (hdiv : ∀ d : ℕ, d ∣ N → 1 < d → ∃ k : ℕ, 0 < k ∧ d = k * F + 1)
    (hcomp : ¬ N.Prime) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ r = u + v ∧ 2 * s = u * v := by
  obtain ⟨d, e, hdN, heN, hde⟩ := (Nat.not_prime_iff_exists_mul_eq hN2).mp hcomp
  have hd2 : 1 < d := by
    by_contra h
    have hh : d = 0 ∨ d = 1 := by omega
    rcases hh with rfl | rfl <;> simp_all
  have he2 : 1 < e := by
    by_contra h
    have hh : e = 0 ∨ e = 1 := by omega
    rcases hh with rfl | rfl <;> simp_all
  obtain ⟨u, hu, hdu⟩ := hdiv d ⟨e, hde.symm⟩ hd2
  obtain ⟨v, hv, hev⟩ := hdiv e ⟨d, by nlinarith [hde]⟩ he2
  have hfactors : N = (u * F + 1) * (v * F + 1) := by rw [← hde, hdu, hev]
  have hprod : u + v ≤ u * v + 1 := by
    have hz : (u : ℤ) + v ≤ u * v + 1 := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ (u : ℤ) - 1 by omega)
        (show (0 : ℤ) ≤ (v : ℤ) - 1 by omega)]
    exact_mod_cast hz
  have hsum : u + v < 2 * F := by
    by_contra h
    have hh : 2 * F ≤ u + v := by omega
    have h1 := mul_le_mul_of_nonneg_right (show 2 * F ≤ u * v + 1 by omega) (Nat.zero_le (F ^ 2))
    have h2 := mul_le_mul_of_nonneg_right hh (Nat.zero_le F)
    nlinarith [hfactors]
  have hReq : R = F * (u * v) + u + v := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < F by omega)
    nlinarith [hN, hfactors]
  have hFmod : F % 2 = 0 := Nat.even_iff.mp hF
  have hRmod : R % 2 = 1 := Nat.odd_iff.mp hRodd
  have hsumodd : (u + v) % 2 = 1 := by
    rw [hReq] at hRmod
    simpa [Nat.add_mod, Nat.mul_mod, hFmod] using hRmod
  have huvmod : (u * v) % 2 = 0 := by
    have hupar : u % 2 = 0 ∨ u % 2 = 1 := by omega
    have hvpar : v % 2 = 0 ∨ v % 2 = 1 := by omega
    rcases hupar with hupar | hupar <;> rcases hvpar with hvpar | hvpar <;>
      simp_all [Nat.add_mod, Nat.mul_mod]
  obtain ⟨w, hw⟩ := Nat.dvd_of_mod_eq_zero huvmod
  have hrem : R % (2 * F) = r := by
    rw [hR]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
  have hrem' : R % (2 * F) = u + v := by
    rw [hReq, hw]
    rw [show F * (2 * w) + u + v = (2 * F) * w + (u + v) by ring]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hsum]
  have hroot : r = u + v := hrem.symm.trans hrem'
  refine ⟨u, v, hu, hv, hroot, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (show 0 < F by omega)
  nlinarith [hR, hReq, hroot]

/-- LEAF. The discriminant identity at the end of the proof of Lemma 8,
p. 27. A factor pair gives the square of u minus v. -/
theorem discriminant_of_roots {r s u v : ℕ} (hr : r = u + v) (hs : 2 * s = u * v) :
    IsSquare ((r : ℤ) ^ 2 - 8 * s) := by
  have hrZ : (r : ℤ) = (u : ℤ) + v := by exact_mod_cast hr
  have hsZ : (2 : ℤ) * s = (u : ℤ) * v := by exact_mod_cast hs
  have hquad : (1 : ℤ) * ((u : ℤ) * u) + (-(r : ℤ)) * u + 2 * s = 0 := by
    nlinarith
  have hd := discrim_eq_sq_of_quadratic_eq_zero hquad
  have he : (r : ℤ) ^ 2 - 8 * s = (2 * (u : ℤ) - r) ^ 2 := by
    dsimp [discrim] at hd
    nlinarith [hd]
  rw [he]
  exact IsSquare.sq _

/-- LEAF. The converse quadratic step implicit in the iff of Lemma 8,
p. 27. A square discriminant and positive s give positive natural roots. -/
theorem roots_of_square {r s : ℕ} (hs : 0 < s) (hdisc : IsSquare ((r : ℤ) ^ 2 - 8 * s)) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ r = u + v ∧ 2 * s = u * v := by
  obtain ⟨z, hz⟩ := hdisc
  let d : ℕ := z.natAbs
  have habs : ((d : ℕ) : ℤ) ^ 2 = z ^ 2 := Int.natAbs_sq z
  have hsq : (r : ℤ) ^ 2 = 8 * s + (d : ℤ) ^ 2 := by nlinarith [hz, habs]
  have hnat : r ^ 2 = 8 * s + d ^ 2 := by exact_mod_cast hsq
  have hlt : d < r := by nlinarith
  have hmod := congrArg (fun x : ℕ => x % 2) hnat
  have hpar : (r + d) % 2 = 0 := by
    have hrpar : r % 2 = 0 ∨ r % 2 = 1 := by omega
    have hdpar : d % 2 = 0 ∨ d % 2 = 1 := by omega
    rcases hrpar with hrpar | hrpar <;> rcases hdpar with hdpar | hdpar <;>
      (norm_num [Nat.add_mod, Nat.mul_mod, pow_two, hrpar, hdpar] at hmod <;>
        norm_num [Nat.add_mod, Nat.mul_mod, pow_two, hrpar, hdpar])
  have hdiffpar : (r - d) % 2 = 0 := by omega
  let u := (r - d) / 2
  let v := (r + d) / 2
  have hu2 : 2 * u = r - d := by dsimp [u]; omega
  have hv2 : 2 * v = r + d := by dsimp [v]; omega
  have hu : 0 < u := by omega
  have hv : 0 < v := by omega
  have hsum : r = u + v := by omega
  refine ⟨u, v, hu, hv, hsum, ?_⟩
  have huZ : (2 : ℤ) * u = (r : ℤ) - d := by
    rw [← Nat.cast_sub hlt.le]
    exact_mod_cast hu2
  have hvZ : (2 : ℤ) * v = (r : ℤ) + d := by exact_mod_cast hv2
  have hprodZ : (4 : ℤ) * u * v = 8 * s := by
    calc
      (4 : ℤ) * u * v = (2 * (u : ℤ)) * (2 * (v : ℤ)) := by ring
      _ = ((r : ℤ) - d) * ((r : ℤ) + d) := by rw [huZ, hvZ]
      _ = 8 * s := by nlinarith [hsq]
  have hp : (2 : ℤ) * s = (u : ℤ) * v := by nlinarith [hprodZ]
  exact_mod_cast hp

/-- LEAF. Expanding the two factors from the quadratic roots recovers N.
The displayed product in the proof of Lemma 8, p. 27. -/
theorem factorization_of_roots {N R F s r u v : ℕ} (hN : N = R * F + 1)
    (hR : R = 2 * F * s + r) (hr : r = u + v) (hs : 2 * s = u * v) :
    N = (u * F + 1) * (v * F + 1) := by
  rw [hN, hR, hr]
  calc
    (2 * F * s + (u + v)) * F + 1 = (2 * s) * F ^ 2 + (u + v) * F + 1 := by ring
    _ = (u * F + 1) * (v * F + 1) := by rw [hs]; ring

/-- LEAF. Both reconstructed factors are proper when F is at least two
and the roots are positive. Lemma 8, p. 27, converse implication. -/
theorem not_prime_of_factorization {N F u v : ℕ} (hF : 2 ≤ F) (hu : 0 < u) (hv : 0 < v)
    (hN : N = (u * F + 1) * (v * F + 1)) : ¬ N.Prime := by
  have huF : 0 < u * F := mul_pos hu (by omega)
  have hvF : 0 < v * F := mul_pos hv (by omega)
  rw [hN]
  exact Nat.not_prime_mul (by omega) (by omega)

/-- Lemma 8 assembled from the divisor property and arithmetic leaves.
No sorry occurs in the assembly. It is CONDITIONAL ON all remaining leaves. -/
theorem lemma8 : lemma8_stmt := by
  intro N R F s r hN2 hF2 hF hcop _hOdd hN hR hr hbound hcert
  obtain ⟨a, ha, hgcd⟩ := hcert
  have hdiv := pocklington_divisors hN2 hF2 hN ha hgcd
  have hRodd := odd_R hcop hF
  constructor
  · intro hp
    by_cases hs : s = 0
    · exact Or.inl hs
    · right
      intro hdisc
      obtain ⟨u, v, hu, hv, hsum, hprod⟩ := roots_of_square (Nat.pos_of_ne_zero hs) hdisc
      exact not_prime_of_factorization hF2 hu hv (factorization_of_roots hN hR hsum hprod) hp
  · intro hc
    by_contra hn
    obtain ⟨u, v, hu, hv, hsum, hprod⟩ :=
      composite_roots hN2 hF2 hF hRodd hN hR hr hbound hdiv hn
    have hspos : 0 < s := by nlinarith [mul_pos hu hv]
    rcases hc with hs | hnot
    · omega
    · exact hnot (discriminant_of_roots hsum hprod)

end LeanLab.RamareSaouter2003.Decomp126b

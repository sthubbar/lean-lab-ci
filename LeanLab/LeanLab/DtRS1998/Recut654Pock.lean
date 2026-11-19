/-
AI wrote this Lean code for CODEX task654.
P0037 Section 5.2 page 212, individual primality certification.
The proofs reuse the existing Pock and PocklingtonB7 arguments with arbitrary fuel.
No cited primality input is assumed. Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Pock
import LeanLab.DtRS1998.PocklingtonB7

namespace LeanLab.DtRS1998.Recut654Pock

open Big LeanLab.Verifications.Pratt

/-- Modular power witnesses force every prime divisor to be one modulo F.
This is the existing Pock argument with the fuel left explicit. -/
theorem factor_congruence (p a Fu : ℕ) (L : List (ℕ × ℕ))
    (hp2 : 2 ≤ p) (hp : p < 2 ^ Fu)
    (hFd : (p - 1) % (L.map fun x => x.1 ^ x.2).prod = 0)
    (hprimes : ∀ x ∈ L, x.1.Prime)
    (hpow : pm Fu a (p - 1) p = 1 % p)
    (hg : ∀ x ∈ L, Nat.gcd ((pm Fu a ((p - 1) / x.1) p + p - 1) % p) p = 1) :
    ∀ q, q.Prime → q ∣ p → (L.map fun x => x.1 ^ x.2).prod ∣ q - 1 := by
  set F := (L.map fun x => x.1 ^ x.2).prod with hFdef
  have hn : p - 1 ≠ 0 := by omega
  have hFn : F ∣ p - 1 := Nat.dvd_of_mod_eq_zero hFd
  -- every prime factor q of p has F ∣ q - 1
  have key : ∀ q, q.Prime → q ∣ p → F ∣ q - 1 := by
    intro q hq hqp
    have := Fact.mk hq
    set x : ZMod q := (a : ZMod q) with hx
    have h1p : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
    have hx1 : x ^ (p - 1) = 1 := by
      rw [hx, ← pm_cast_dvd Fu a (p - 1) p q hqp (by omega), hpow, h1p]
      simp
    have hx0 : x ≠ 0 := by
      intro h0; rw [h0, zero_pow hn] at hx1; exact zero_ne_one hx1
    have ho1 : orderOf x ∣ p - 1 := orderOf_dvd_of_pow_eq_one hx1
    have ho2 : orderOf x ∣ q - 1 := ZMod.orderOf_dvd_card_sub_one hx0
    refine dvd_trans (dvd_of_order (orderOf x) (p - 1) F hn ho1 hFn ?_) ho2
    intro r hr hrF hod
    -- r is one of the listed primes
    obtain ⟨y, hy, hyd⟩ := (Nat.prime_iff.mp hr).dvd_prod_iff.mp hrF
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
    have hre : r = e.1 :=
      (Nat.prime_dvd_prime_iff_eq hr (hprimes e he)).mp (hr.dvd_of_dvd_pow hyd)
    subst hre
    have hxr : x ^ ((p - 1) / e.1) = 1 := (orderOf_dvd_iff_pow_eq_one).mp hod
    have hlt : (p - 1) / e.1 < 2 ^ Fu := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    have hc := pm_cast_dvd Fu a ((p - 1) / e.1) p q hqp hlt
    rw [← hx, hxr] at hc
    set t := pm Fu a ((p - 1) / e.1) p
    have hz : (((t + p - 1) % p : ℕ) : ZMod q) = 0 := by
      have hm : (t + p - 1) % p % q = (t + p - 1) % q := Nat.mod_mod_of_dvd _ hqp
      rw [(ZMod.natCast_eq_natCast_iff' _ _ q).mpr hm]
      have hp0 : ((p : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff p q).mpr hqp
      have : t + p - 1 = t + (p - 1) := by omega
      rw [this, Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ p), hp0, hc]
      simp
    have hqd : q ∣ (t + p - 1) % p := (ZMod.natCast_eq_zero_iff _ q).mp hz
    have hg1 := hg e he
    have : q ∣ 1 := by
      rw [← hg1]; exact Nat.dvd_gcd hqd hqp
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  exact key

/-- The cube-root arithmetic criterion from the existing BLS proof.
Every prime divisor is one modulo F and the base F discriminant is not a square. -/
theorem prime_of_factor_divisibility (n F t : ℕ) (hn : 2 ≤ n)
    (hcube : n < F * F * F)
    (fac : ∀ r, r.Prime → r ∣ n → F ∣ r - 1)
    (hsq : (n - 1) / F % F * ((n - 1) / F % F) < 4 * ((n - 1) / F / F) ∨
      (t * t < (n - 1) / F % F * ((n - 1) / F % F) - 4 * ((n - 1) / F / F) ∧
        (n - 1) / F % F * ((n - 1) / F % F) - 4 * ((n - 1) / F / F) < (t + 1) * (t + 1))) :
    n.Prime := by
  by_contra hnp
  set r := n.minFac with hr
  have hrp : r.Prime := Nat.minFac_prime (by omega)
  have hrn : r ∣ n := Nat.minFac_dvd n
  have hrsq : r ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  set s := n / r with hs
  have hnrs : n = r * s := (Nat.mul_div_cancel' hrn).symm
  have hrs : r ≤ s := by
    have : r * r ≤ r * s := by rw [← hnrs, ← pow_two]; exact hrsq
    exact Nat.le_of_mul_le_mul_left this hrp.pos
  have hFr := fac r hrp hrn
  have hF0 : 0 < F := by
    rcases Nat.eq_zero_or_pos F with h | h
    · rw [h] at hcube; simp at hcube
    · exact h
  have hr1 : F + 1 ≤ r := by
    have := Nat.le_of_dvd (by have := hrp.two_le; omega) hFr; omega
  have hsp : s.Prime := by
    by_contra hsn
    have hs2 : 2 ≤ s := le_trans hrp.two_le hrs
    set v := s.minFac
    have hvp : v.Prime := Nat.minFac_prime (by omega)
    have hvs : v ∣ s := Nat.minFac_dvd s
    have hvsq : v ^ 2 ≤ s := Nat.minFac_sq_le_self (by omega) hsn
    have hv1 : F + 1 ≤ v := by
      have := Nat.le_of_dvd (by have := hvp.two_le; omega)
        (fac v hvp (hvs.trans (Dvd.intro_left _ hnrs.symm)))
      omega
    have : (F + 1) * ((F + 1) * (F + 1)) ≤ n := by
      rw [hnrs]
      apply Nat.mul_le_mul hr1
      calc (F + 1) * (F + 1) ≤ v * v := Nat.mul_le_mul hv1 hv1
        _ = v ^ 2 := by ring
        _ ≤ s := hvsq
    nlinarith
  have hFs := fac s hsp (Dvd.intro_left _ hnrs.symm)
  obtain ⟨x, hx⟩ := hFr
  obtain ⟨y, hy⟩ := hFs
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · rw [h] at hx; have := hrp.two_le; omega
    · exact h
  have hy1 : 1 ≤ y := by
    rcases Nat.eq_zero_or_pos y with h | h
    · rw [h] at hy; have := hsp.two_le; omega
    · exact h
  have hn' : n = (1 + x * F) * (1 + y * F) := by
    rw [hnrs]
    have e1 : r = 1 + x * F := by have := hrp.two_le; rw [mul_comm, ← hx]; omega
    have e2 : s = 1 + y * F := by have := hsp.two_le; rw [mul_comm, ← hy]; omega
    rw [e1, e2]
  obtain ⟨d1, d2⟩ := PocklingtonB7.bls_digits F x y n hx1 hy1 hn' hcube
  rw [d1, d2] at hsq
  rcases le_total y x with h | h
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
    have hD : (y + e + y) * (y + e + y) - 4 * ((y + e) * y) = e * e := by
      have : (y + e + y) * (y + e + y) = 4 * ((y + e) * y) + e * e := by ring
      omega
    rw [hD] at hsq
    rcases hsq with h1 | ⟨h1, h2⟩
    · nlinarith
    · have a1 := Nat.mul_self_lt_mul_self_iff.mp h1
      have a2 := Nat.mul_self_lt_mul_self_iff.mp h2
      omega
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
    have hD : (x + (x + e)) * (x + (x + e)) - 4 * (x * (x + e)) = e * e := by
      have : (x + (x + e)) * (x + (x + e)) = 4 * (x * (x + e)) + e * e := by ring
      omega
    rw [hD] at hsq
    rcases hsq with h1 | ⟨h1, h2⟩
    · nlinarith
    · have a1 := Nat.mul_self_lt_mul_self_iff.mp h1
      have a2 := Nat.mul_self_lt_mul_self_iff.mp h2
      omega

end LeanLab.DtRS1998.Recut654Pock

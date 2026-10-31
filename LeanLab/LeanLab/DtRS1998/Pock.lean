/-
P0037, unit U-0943, run 20261018T1303Z-6675. A Pocklington certificate chain checker: p is prime
when F divides p - 1, p < (F + 1)^2, F is a product of certified primes r, a^(p-1) = 1 mod p and
gcd(a^((p-1)/r) - 1, p) = 1 for each r. Only part of p - 1 needs factoring, which a Lucas
certificate cannot avoid. Soundness proved once, from orderOf in ZMod q for each prime q dividing p.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
-/
import LeanLab.DtRS1998.BigCert

namespace LeanLab.DtRS1998.Big

open LeanLab.Verifications.Pratt

theorem pm_cast_dvd (fuel a e p q : ℕ) (hq : q ∣ p) (he : e < 2 ^ fuel) :
    ((pm fuel a e p : ℕ) : ZMod q) = (a : ZMod q) ^ e := by
  have h := congrArg (ZMod.castHom hq (ZMod q)) (pm_cast fuel a e p he)
  simp only [map_pow, map_natCast] at h
  exact h

/-- If `o ∣ n` and `o ∤ n / r` for every prime `r ∣ F`, where `F ∣ n`, then `F ∣ o`. -/
theorem dvd_of_order (o n F : ℕ) (hn : n ≠ 0) (hon : o ∣ n) (hF : F ∣ n)
    (hr : ∀ r, r.Prime → r ∣ F → ¬ o ∣ n / r) : F ∣ o := by
  have ho : o ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hon)
  have hF0 : F ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hF)
  rw [← Nat.factorization_prime_le_iff_dvd hF0 ho]
  intro r hrp
  by_contra hlt
  push Not at hlt
  have hrF : r ∣ F := by
    by_contra h
    rw [Nat.factorization_eq_zero_of_not_dvd h] at hlt
    omega
  apply hr r hrp hrF
  have hrn : r ∣ n := dvd_trans hrF hF
  have hnr : n / r ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hrn) hrp.pos
    omega
  rw [← Nat.factorization_prime_le_iff_dvd ho hnr]
  intro s hs
  rw [Nat.factorization_div hrn]
  have h1 := (Nat.factorization_prime_le_iff_dvd ho hn).mpr hon s hs
  have h2 := (Nat.factorization_prime_le_iff_dvd hF0 hn).mpr hF r hrp
  rw [hrp.factorization]
  simp only [Finsupp.coe_tsub, Pi.sub_apply]
  by_cases hsr : s = r
  · subst hsr; simp; omega
  · rw [Finsupp.single_apply, if_neg (Ne.symm hsr)]; omega

theorem pock (p a Fu : ℕ) (L : List (ℕ × ℕ)) (hp2 : 2 ≤ p) (hp : p < 2 ^ Fu)
    (hFd : (p - 1) % (L.map fun x => x.1 ^ x.2).prod = 0)
    (hbig : p < ((L.map fun x => x.1 ^ x.2).prod + 1) ^ 2)
    (hprimes : ∀ x ∈ L, x.1.Prime)
    (hpow : pm Fu a (p - 1) p = 1 % p)
    (hg : ∀ x ∈ L, Nat.gcd ((pm Fu a ((p - 1) / x.1) p + p - 1) % p) p = 1) : p.Prime := by
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
  by_contra hnp
  have hmf : p.minFac.Prime := Nat.minFac_prime (by omega)
  have hFq := key _ hmf (Nat.minFac_dvd p)
  have hle : F + 1 ≤ p.minFac := by
    have h2 := hmf.two_le
    have := Nat.le_of_dvd (by omega) hFq
    omega
  have hsq := Nat.minFac_sq_le_self (by omega : 0 < p) hnp
  have : (F + 1) ^ 2 ≤ p.minFac ^ 2 := Nat.pow_le_pow_left hle 2
  omega

/-- One Pocklington certificate `(p, a, L)`, `L` a partial factorization of `p - 1`. -/
def pockK (known : List ℕ) : Cert → Bool
  | (p, a, L) =>
    let Fu := p.log2 + 1
    let F := (L.map fun x => x.1 ^ x.2).prod
    decide (2 ≤ p) && ((p - 1) % F == 0) && decide (p < (F + 1) ^ 2) &&
      L.all (fun x => known.contains x.1 || primeB x.1) && (pm Fu a (p - 1) p == 1 % p) &&
      L.all (fun x => Nat.gcd ((pm Fu a ((p - 1) / x.1) p + p - 1) % p) p == 1)

theorem prime_of_pockK {known : List ℕ} (hk : ∀ k ∈ known, k.Prime) {c : Cert}
    (h : pockK known c = true) : c.1.Prime := by
  obtain ⟨p, a, L⟩ := c
  simp only [pockK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    Bool.or_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨h2, hFd⟩, hbig⟩, hfac⟩, hpow⟩, hg⟩ := h
  refine pock p a (p.log2 + 1) L h2 Nat.lt_log2_self hFd hbig ?_ hpow hg
  intro x hx
  rcases hfac x hx with h | h
  · exact hk _ h
  · exact primeB_sound h

/-- A Pocklington chain: each certificate may use the primes of the earlier ones. -/
def chainP : List ℕ → List Cert → Bool
  | _, [] => true
  | known, c :: t => pockK known c && chainP (c.1 :: known) t

theorem chainP_sound : ∀ (C : List Cert) (known : List ℕ), (∀ k ∈ known, k.Prime) →
    chainP known C = true → ∀ c ∈ C, c.1.Prime := by
  intro C
  induction C with
  | nil => intro _ _ _ c hc; simp at hc
  | cons c t ih =>
    intro known hk h c' hc'
    simp only [chainP, Bool.and_eq_true] at h
    have hc : c.1.Prime := prime_of_pockK hk h.1
    have hk' : ∀ k ∈ c.1 :: known, k.Prime := by
      intro k hk2
      rcases List.mem_cons.mp hk2 with rfl | hk2
      · exact hc
      · exact hk k hk2
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact hc
    · exact ih _ hk' h.2 c' hc'

theorem chainP_append : ∀ (known : List ℕ) (A B : List Cert),
    chainP known (A ++ B) = (chainP known A && chainP ((A.map Prod.fst).reverse ++ known) B) := by
  intro known A
  induction A generalizing known with
  | nil => intro B; simp [chainP]
  | cons c t ih =>
    intro B
    simp only [List.cons_append, chainP, ih, List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, Bool.and_assoc, List.nil_append]

theorem all_prime_overP {S C : List Cert} (hS : chainP [] S = true)
    (hC : C.all (pockK (S.map Prod.fst)) = true) : ∀ p ∈ C.map Prod.fst, p.Prime := by
  have hk : ∀ k ∈ S.map Prod.fst, k.Prime := by
    intro p hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    exact chainP_sound S [] (by simp) hS c hc
  intro p hp
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  exact prime_of_pockK hk (List.all_eq_true.mp hC c hc)

/-- Sanity: 1000003 from the single factor 166667 of p - 1 = 2 · 3 · 166667. -/
example : (1000003 : ℕ).Prime :=
  prime_of_pockK (known := []) (by simp) (c := (1000003, 2, [(166667, 1)])) (by decide +kernel)

end LeanLab.DtRS1998.Big

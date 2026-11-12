/-
ROUTE BURST 7, DtRS1998 first_family_remaining.
AI wrote this Lean code. Binary Goldbach is OPEN.

P0037 Section 5.1 page 211, the finite primality certification paragraph:
the large candidates of Table 1 page 213 are proved prime individually.
Here that step is done by the classical Pocklington N - 1 test,
H. C. Pocklington 1914, Proc. Cambridge Phil. Soc. 18, pages 29 to 30,
in the form of Brillhart, Lehmer and Selfridge 1975, Math. Comp. 29,
Theorem 4: if N - 1 = F R with F^2 > N, and for every prime p dividing F
there is a with a^(N-1) = 1 mod N and gcd(a^((N-1)/p) - 1, N) = 1,
then N is prime. One witness a serves all p of one certificate here.
When only F^3 > N holds, the same conditions plus Brillhart, Lehmer and
Selfridge 1975 Theorem 5 are used: with R = (N-1)/F = c2 F + c1 and
0 <= c1 < F, N is prime if c1^2 - 4 c2 is not a square.

The Boolean checker `chainOK` below is proved sound once, so a list of
certificate chains is checked by one `decide +kernel` call. Prime factors
below 2^16 of N - 1 are checked by the lab trial division `LeanLab.primeB`.
Larger factors must be certified earlier in the same chain.
`pm` is a copy of `LeanLab.Verifications.Pratt.pm`, and `pm_cast` a copy of
its proof, made here so this module needs no Verifications import.
No native_decide, no axioms.
-/
import Mathlib
import LeanLab.Common.Goldbach

namespace LeanLab.DtRS1998.PocklingtonB7

/-- Binary modular power with fuel, a copy of `LeanLab.Verifications.Pratt.pm`. -/
def pm : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 1
  | fuel + 1, a, e, m =>
    if e = 0 then 1 % m else
      let h := pm fuel a (e / 2) m
      if e % 2 = 1 then h * h % m * a % m else h * h % m

/-- A copy of `LeanLab.Verifications.Pratt.pm_cast`. -/
theorem pm_cast : ∀ fuel a e m, e < 2 ^ fuel →
    ((pm fuel a e m : ℕ) : ZMod m) = (a : ZMod m) ^ e := by
  intro fuel
  induction fuel with
  | zero => intro a e m he; simp at he; subst he; simp [pm]
  | succ k ih =>
    intro a e m he
    simp only [pm]
    by_cases h0 : e = 0
    · subst h0; simp
    · rw [if_neg h0]
      have hlt : e / 2 < 2 ^ k := by rw [pow_succ] at he; omega
      have IH := ih a (e / 2) m hlt
      have he2 : e = 2 * (e / 2) + e % 2 := (Nat.div_add_mod e 2).symm
      by_cases h1 : e % 2 = 1
      · rw [if_pos h1]
        simp only [Nat.cast_mul, ZMod.natCast_mod, IH]
        conv_rhs => rw [he2, h1, pow_add, pow_mul, pow_one]
        ring
      · rw [if_neg h1]
        have h1' : e % 2 = 0 := by omega
        simp only [Nat.cast_mul, ZMod.natCast_mod, IH]
        conv_rhs => rw [he2, h1', add_zero, pow_mul]
        ring

/-- The fuel used for every modular power; every certified number is below `2 ^ K`. -/
def K : ℕ := 400

/-- The product of the listed prime powers. -/
def prodPow : List (ℕ × ℕ) → ℕ
  | [] => 1
  | x :: t => x.1 ^ x.2 * prodPow t

/-- The listed primes are strictly increasing and above `lo`. -/
def chain : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | lo, x :: t => decide (lo < x.1) && chain x.1 t

/-- A certificate: the number `n`, one witness `a`, a square test number `t` used only
by the cube root test, and the factored part of `n - 1` as a list of prime powers. -/
abbrev Cert := ℕ × ℕ × ℕ × List (ℕ × ℕ)

/-- The size test: Pocklington's square root bound, or the cube root bound of
Brillhart Lehmer Selfridge 1975 Theorem 5 with its non square test. -/
def sizeOK (n t F : ℕ) : Bool :=
  decide (n < F * F) ||
    (decide (n < F * F * F) &&
      (decide ((n - 1) / F % F * ((n - 1) / F % F) < 4 * ((n - 1) / F / F)) ||
        (decide (t * t < (n - 1) / F % F * ((n - 1) / F % F) - 4 * ((n - 1) / F / F)) &&
          decide ((n - 1) / F % F * ((n - 1) / F % F) - 4 * ((n - 1) / F / F) <
            (t + 1) * (t + 1)))))

/-- Boolean Pocklington check of one certificate, where `pr` lists numbers already
certified prime. -/
def certOK (pr : List ℕ) : Cert → Bool
  | (n, a, t, L) =>
    decide (2 ≤ n) && decide (n < 2 ^ K) && chain 0 L &&
      ((n - 1) % prodPow L == 0) && sizeOK n t (prodPow L) &&
      L.all (fun x => pr.elem x.1 || (decide (x.1 < 65536) && LeanLab.primeB x.1)) &&
      (pm K a (n - 1) n == 1 % n) &&
      L.all (fun x => Nat.gcd (pm K a ((n - 1) / x.1) n + n - 1) n == 1)

/-- A chain of certificates, each allowed to use the earlier ones. -/
def chainOK : List ℕ → List Cert → Bool
  | _, [] => true
  | pr, c :: cs => certOK pr c && chainOK (c.1 :: pr) cs

/-- The number certified last by a chain, or 0 for the empty chain. -/
def lastP (ch : List Cert) : ℕ := (ch.getLast?.map Prod.fst).getD 0

theorem pow_dvd_prodPow : ∀ (L : List (ℕ × ℕ)) (x : ℕ × ℕ), x ∈ L → x.1 ^ x.2 ∣ prodPow L
  | [], _, h => by simp at h
  | y :: t, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Dvd.intro _ rfl
    · exact Dvd.dvd.mul_left (pow_dvd_prodPow t x h) _

theorem chain_lt : ∀ (L : List (ℕ × ℕ)) (lo : ℕ), chain lo L = true → ∀ x ∈ L, lo < x.1
  | [], _, _, x, hx => by simp at hx
  | y :: t, lo, h, x, hx => by
    simp only [chain, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 (chain_lt t y.1 h.2 x hx)

theorem not_dvd_prodPow (p : ℕ) (hp : p.Prime) :
    ∀ (L : List (ℕ × ℕ)), (∀ y ∈ L, y.1.Prime ∧ p < y.1) → ¬ p ∣ prodPow L
  | [], _ => by simp [prodPow, hp.ne_one]
  | y :: t, h => by
    intro hd
    simp only [prodPow] at hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
    · have hy := h y (List.mem_cons_self ..)
      have := (Nat.prime_dvd_prime_iff_eq hp hy.1).mp (hp.dvd_of_dvd_pow hd)
      omega
    · exact not_dvd_prodPow p hp t (fun z hz => h z (List.mem_cons_of_mem _ hz)) hd

theorem prodPow_dvd (u : ℕ) : ∀ (L : List (ℕ × ℕ)) (lo : ℕ), chain lo L = true →
    (∀ x ∈ L, x.1.Prime) → (∀ x ∈ L, x.1 ^ x.2 ∣ u) → prodPow L ∣ u
  | [], _, _, _, _ => by simp [prodPow]
  | y :: t, lo, hc, hp, hd => by
    simp only [chain, Bool.and_eq_true] at hc
    simp only [prodPow]
    have hy := hp y (List.mem_cons_self ..)
    have hcop : Nat.Coprime (y.1 ^ y.2) (prodPow t) := by
      apply Nat.Coprime.pow_left
      rw [Nat.Prime.coprime_iff_not_dvd hy]
      exact not_dvd_prodPow y.1 hy t (fun z hz =>
        ⟨hp z (List.mem_cons_of_mem _ hz), chain_lt t y.1 hc.2 z hz⟩)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (hd y (List.mem_cons_self ..))
      (prodPow_dvd u t y.1 hc.2 (fun z hz => hp z (List.mem_cons_of_mem _ hz))
        (fun z hz => hd z (List.mem_cons_of_mem _ hz)))

/-- The core of Pocklington's theorem, Brillhart Lehmer Selfridge 1975 Theorem 4:
every prime factor `r` of `n` satisfies `r = 1 mod F`. -/
theorem pock_factor (n a : ℕ) (L : List (ℕ × ℕ)) (hn : 2 ≤ n) (hK : n < 2 ^ K)
    (hc : chain 0 L = true) (hprimes : ∀ x ∈ L, x.1.Prime)
    (hF : (n - 1) % prodPow L = 0)
    (hfer : pm K a (n - 1) n = 1 % n)
    (hgcd : ∀ x ∈ L, Nat.gcd (pm K a ((n - 1) / x.1) n + n - 1) n = 1)
    (r : ℕ) (hrp : r.Prime) (hrn : r ∣ n) : prodPow L ∣ r - 1 := by
  have : Fact r.Prime := ⟨hrp⟩
  have key : ∀ e, e < 2 ^ K → ((pm K a e n : ℕ) : ZMod r) = (a : ZMod r) ^ e := by
    intro e he
    have h := congrArg (ZMod.castHom hrn (ZMod r)) (pm_cast K a e n he)
    simpa [map_pow, map_natCast] using h
  have hn0 : ((n : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff n r).mpr hrn
  set b : ZMod r := (a : ZMod r)
  have hb1 : b ^ (n - 1) = 1 := by
    rw [← key (n - 1) (by omega), hfer, Nat.mod_eq_of_lt (by omega)]
    simp
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hb1
    exact zero_ne_one hb1
  set u := orderOf b
  have hu_n : u ∣ n - 1 := orderOf_dvd_of_pow_eq_one hb1
  have hu_r : u ∣ r - 1 := orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hb0)
  have hpow : ∀ x ∈ L, x.1 ^ x.2 ∣ u := by
    intro x hx
    have hxp := hprimes x hx
    have hne : b ^ ((n - 1) / x.1) ≠ 1 := by
      intro h1
      have hle : (n - 1) / x.1 < 2 ^ K := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
      have hz : ((pm K a ((n - 1) / x.1) n + n - 1 : ℕ) : ZMod r) = 0 := by
        rw [Nat.cast_sub (by omega), Nat.cast_add, key _ hle, h1, hn0]
        simp
      have hd : r ∣ pm K a ((n - 1) / x.1) n + n - 1 := (ZMod.natCast_eq_zero_iff _ r).mp hz
      have := Nat.dvd_gcd hd hrn
      rw [hgcd x hx] at this
      exact hrp.one_lt.ne' (Nat.dvd_one.mp this)
    have hndiv : ¬ u ∣ (n - 1) / x.1 := fun h => hne (orderOf_dvd_iff_pow_eq_one.mp h)
    obtain ⟨w, hw⟩ := hu_n
    have hpw : ¬ x.1 ∣ w := by
      rintro ⟨w', rfl⟩
      apply hndiv
      have : (n - 1) / x.1 = u * w' := by
        rw [hw, show u * (x.1 * w') = x.1 * (u * w') by ring]
        exact Nat.mul_div_cancel_left _ hxp.pos
      rw [this]; exact Dvd.intro _ rfl
    have hxF : x.1 ^ x.2 ∣ n - 1 :=
      (pow_dvd_prodPow L x hx).trans (Nat.dvd_of_mod_eq_zero hF)
    rw [hw] at hxF
    exact Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hxp).mpr hpw)) hxF
  exact (prodPow_dvd u L 0 hc hprimes hpow).trans hu_r

/-- Pocklington's theorem, Brillhart Lehmer Selfridge 1975 Theorem 4 form:
the factored part `F` of `n - 1` exceeds the square root of `n`. -/
theorem pocklington (n a : ℕ) (L : List (ℕ × ℕ)) (hn : 2 ≤ n) (hK : n < 2 ^ K)
    (hc : chain 0 L = true) (hprimes : ∀ x ∈ L, x.1.Prime)
    (hF : (n - 1) % prodPow L = 0) (hsq : n < prodPow L * prodPow L)
    (hfer : pm K a (n - 1) n = 1 % n)
    (hgcd : ∀ x ∈ L, Nat.gcd (pm K a ((n - 1) / x.1) n + n - 1) n = 1) : n.Prime := by
  by_contra hnp
  set r := n.minFac with hr
  have hrp : r.Prime := Nat.minFac_prime (by omega)
  have hrn : r ∣ n := Nat.minFac_dvd n
  have hrsq : r ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have hFr : prodPow L ≤ r - 1 := Nat.le_of_dvd (by have := hrp.two_le; omega)
    (pock_factor n a L hn hK hc hprimes hF hfer hgcd r hrp hrn)
  have h2 : prodPow L * prodPow L ≤ (r - 1) * (r - 1) := Nat.mul_le_mul hFr hFr
  have h3 : (r - 1) * (r - 1) < r ^ 2 := by
    have := hrp.two_le
    rw [pow_two]; exact Nat.mul_lt_mul'' (by omega) (by omega)
  omega

/-- The arithmetic heart of Brillhart Lehmer Selfridge 1975 Theorem 5: if
`n = (1 + x F) (1 + y F)` with `x, y ≥ 1` and `n < F^3`, then the base `F` digits
`c1 = R mod F` and `c2 = R / F` of `R = (n - 1) / F` satisfy `c1 = x + y`, `c2 = x y`. -/
theorem bls_digits (F x y n : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hn : n = (1 + x * F) * (1 + y * F)) (h3 : n < F * F * F) :
    (n - 1) / F % F = x + y ∧ (n - 1) / F / F = x * y := by
  have hF : 0 < F := by
    rcases Nat.eq_zero_or_pos F with h | h
    · subst h; simp at h3
    · exact h
  have hR : (n - 1) / F = F * (x * y) + (x + y) := by
    have : n - 1 = F * (F * (x * y) + (x + y)) := by subst hn; ring_nf; omega
    rw [this, Nat.mul_div_cancel_left _ hF]
  have hxy : x * y < F := by
    by_contra h
    push_neg at h
    have : F * F * F ≤ n := by
      subst hn
      have h1 : F * F * F ≤ (x * y) * (F * F) := by
        calc F * F * F = F * (F * F) := by ring
          _ ≤ (x * y) * (F * F) := Nat.mul_le_mul_right _ h
      nlinarith
    omega
  have hsum : x + y < F := by
    by_contra h
    push_neg at h
    have h1 : x + y ≤ x * y + 1 := by nlinarith
    have h4 : F * F * F + 1 ≤ n := by
      subst hn
      have e1 : F ≤ x + y := h
      have e2 : F ≤ x * y + 1 := le_trans e1 h1
      have e3 : F * F ≤ (x + y) * F := Nat.mul_le_mul_right _ e1
      have e4 : F * (F * F) ≤ (x * y + 1) * (F * F) := Nat.mul_le_mul_right _ e2
      nlinarith
    omega
  rw [hR]
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hsum]
  · rw [Nat.mul_add_div hF, Nat.div_eq_of_lt hsum, add_zero]

/-- Brillhart Lehmer Selfridge 1975 Theorem 5: the factored part `F` of `n - 1`
exceeds the cube root of `n`, and `c1^2 - 4 c2` is not a square, certified by
`t` with `t^2 < c1^2 - 4 c2 < (t + 1)^2`, or by `c1^2 < 4 c2`. -/
theorem bls (n a t : ℕ) (L : List (ℕ × ℕ)) (hn : 2 ≤ n) (hK : n < 2 ^ K)
    (hc : chain 0 L = true) (hprimes : ∀ x ∈ L, x.1.Prime)
    (hF : (n - 1) % prodPow L = 0) (hcube : n < prodPow L * prodPow L * prodPow L)
    (hfer : pm K a (n - 1) n = 1 % n)
    (hgcd : ∀ x ∈ L, Nat.gcd (pm K a ((n - 1) / x.1) n + n - 1) n = 1)
    (hsq : (n - 1) / prodPow L % prodPow L * ((n - 1) / prodPow L % prodPow L) <
        4 * ((n - 1) / prodPow L / prodPow L) ∨
      (t * t < (n - 1) / prodPow L % prodPow L * ((n - 1) / prodPow L % prodPow L) -
          4 * ((n - 1) / prodPow L / prodPow L) ∧
        (n - 1) / prodPow L % prodPow L * ((n - 1) / prodPow L % prodPow L) -
          4 * ((n - 1) / prodPow L / prodPow L) < (t + 1) * (t + 1))) : n.Prime := by
  set F := prodPow L with hFdef
  have fac := pock_factor n a L hn hK hc hprimes hF hfer hgcd
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
  obtain ⟨d1, d2⟩ := bls_digits F x y n hx1 hy1 hn' hcube
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

theorem certOK_sound (pr : List ℕ) (hpr : ∀ p ∈ pr, p.Prime) (c : Cert)
    (h : certOK pr c = true) : c.1.Prime := by
  obtain ⟨n, a, t, L⟩ := c
  simp only [certOK, sizeOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    Bool.or_eq_true, List.elem_eq_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h2, hK⟩, hc⟩, hF⟩, hsz⟩, hpr'⟩, hfer⟩, hgcd⟩ := h
  have hprimes : ∀ x ∈ L, x.1.Prime := by
    intro x hx
    rcases hpr' x hx with h | h
    · exact hpr _ h
    · exact LeanLab.primeB_sound h.2
  rcases hsz with hsq | ⟨hcube, hns⟩
  · exact pocklington n a L h2 hK hc hprimes hF hsq hfer hgcd
  · exact bls n a t L h2 hK hc hprimes hF hcube hfer hgcd hns

theorem chainOK_sound : ∀ (cs : List Cert) (pr : List ℕ), (∀ p ∈ pr, p.Prime) →
    chainOK pr cs = true → ∀ c ∈ cs, c.1.Prime
  | [], _, _, _, c, hc => by simp at hc
  | d :: cs, pr, hpr, h, c, hc => by
    simp only [chainOK, Bool.and_eq_true] at h
    have hd := certOK_sound pr hpr d h.1
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hd
    · exact chainOK_sound cs (d.1 :: pr)
        (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hd
          · exact hpr p hp) h.2 c hc

/-- A nonempty checked chain certifies its last number. -/
def chainB (ch : List Cert) : Bool := !ch.isEmpty && chainOK [] ch

theorem lastP_prime (ch : List Cert) (h : chainB ch = true) : (lastP ch).Prime := by
  simp only [chainB, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨hne, h⟩ := h
  have hmem := List.getLast_mem hne
  have := chainOK_sound ch [] (by simp) h _ hmem
  simpa [lastP, List.getLast?_eq_some_getLast hne] using this

/-- Every number of `l` is prime when `l` is the list of last numbers of checked chains. -/
theorem primes_of_chains (C : List (List Cert)) (l : List ℕ) (hl : C.map lastP = l)
    (hC : C.all chainB = true) : ∀ q ∈ l, q.Prime := by
  intro q hq
  rw [← hl] at hq
  obtain ⟨ch, hch, rfl⟩ := List.mem_map.mp hq
  exact lastP_prime ch (List.all_eq_true.mp hC ch hch)

#print axioms primes_of_chains

end LeanLab.DtRS1998.PocklingtonB7

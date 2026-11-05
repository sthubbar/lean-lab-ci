import LeanLab.OpenProblems.Erdos9
import LeanLab.OpenProblems.Lemoine
import LeanLab.OpenProblems.Erdos17
import LeanLab.BrunGap.Final

/-!
# OpenProblems, named route lemmas for the provers

Unit U-1603, 2026-11-02. AI wrote the Lean code. All three named route lemmas below are PROVED,
0 sorry since gate lmerge 20261103T2314Zw. The file imports `LeanLab.BrunGap.Final`, the one import
exception Steve granted live, filed lomos 20261103T2027Z. The sealed open problems themselves are
`def`s in their own files. None of these lemmas settles its open problem. Each one is weaker than
the problem, and closing one is a step, not a solution. Erdős 273 has no row here: its target is a
search winner fed to `Erdos273.statement_of_check`.
-/

namespace LeanLab.OpenProblems

open Erdos9 Lemoine Erdos17

set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

/-! ### Private support for `route_erdos9A_infinite` -/

/-- `45592577 = 2^12 * 11131 + 1`, the least prime factor of the Fermat number `2^1024 + 1`. -/
private abbrev cpk : ℕ := 45592577

/-- The cofactor `(2^1024 + 1) / 45592577`. -/
private abbrev cfac : ℕ :=
  3942951359960012586542991835686376608231592127249807732373409846031135195659174148737161255930050543559319182152642816343958573976075461198274610155058226350701077796608546283231637018483208223116080561800334422176622099740983337736621316898600121619871377542107047343253864459964167331555646795960321

private lemma bk_gk : cpk * cfac = 2 ^ 1024 + 1 := by decide

private lemma gk_pos : 0 < cfac := by decide

private lemma gk_lt : cfac < 2 ^ 1000 := by decide

private lemma gk_odd : cfac % 2 = 1 := by decide

/-- `fprod N` is the product of the Fermat divisors `B_i`, `i < N`, in Crocker's construction. -/
private abbrev fprod (N : ℕ) : ℕ := (2 ^ (2 ^ N) - 1) / cfac

/-- The `i`-th Fermat number. -/
private abbrev fnum (i : ℕ) : ℕ := 2 ^ (2 ^ i) + 1

private lemma fermat_odd (i : ℕ) : fnum i % 2 = 1 := by
  have h2 : 2 ∣ 2 ^ (2 ^ i) := by
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ i = k + 1 := ⟨2 ^ i - 1, by have := Nat.two_pow_pos i; omega⟩
    rw [hk, pow_succ]
    exact ⟨2 ^ k, by ring⟩
  simp only [fnum]
  omega

/-- `x + 1` divides `x ^ k - 1` for even `k`. -/
private lemma add_one_dvd_pow_sub_one_int (x : ℤ) {k : ℕ} (hk : Even k) : (x + 1) ∣ x ^ k - 1 := by
  have h := sub_one_dvd_pow_sub_one (-x : ℤ) k
  rw [hk.neg_pow] at h
  rwa [show -x - 1 = -(x + 1) by ring, Int.neg_dvd] at h

/-- `x + 1` divides `x ^ k + 1` for odd `k`. -/
private lemma add_one_dvd_pow_add_one_int (x : ℤ) {k : ℕ} (hk : Odd k) : (x + 1) ∣ x ^ k + 1 := by
  have h := sub_one_dvd_pow_sub_one (-x : ℤ) k
  rw [hk.neg_pow] at h
  have h1 : -x - 1 = -(x + 1) := by ring
  have h2 : -x ^ k - 1 = -(x ^ k + 1) := by ring
  rw [h1, h2] at h
  have h3 := Int.neg_dvd.mp h
  rwa [Int.dvd_neg] at h3

private lemma fermat_dvd_nat (i N : ℕ) (h : i < N) : fnum i ∣ 2 ^ (2 ^ N) - 1 := by
  have hpos : 0 < N - i := Nat.sub_pos_of_lt h
  obtain ⟨j, hj⟩ : ∃ j, N - i = j + 1 := ⟨N - i - 1, by omega⟩
  have hsplit : 2 ^ N = 2 ^ i * 2 ^ (N - i) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' h.le]
  have hval : (fnum i : ℤ) ∣ ((2 : ℤ)) ^ (2 ^ N) - 1 := by
    have : ((2 : ℤ)) ^ (2 ^ N) = ((2 : ℤ) ^ (2 ^ i)) ^ (2 ^ (N - i)) := by
      rw [hsplit, pow_mul]
    rw [this]
    have : (fnum i : ℤ) = (2 : ℤ) ^ (2 ^ i) + 1 := by simp [fnum]
    rw [this]
    refine add_one_dvd_pow_sub_one_int _ ?_
    rw [hj]
    exact ⟨2 ^ j, by rw [pow_succ]; ring⟩
  have hcast : ((2 ^ (2 ^ N) - 1 : ℕ) : ℤ) = (2 : ℤ) ^ (2 ^ N) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat]
    push_cast
    ring
  have h3 : ((fnum i : ℕ) : ℤ) ∣ ((2 ^ (2 ^ N) - 1 : ℕ) : ℤ) := by
    rw [hcast]; exact hval
  exact Int.natCast_dvd_natCast.mp h3

private lemma fermat_coprime {i j : ℕ} (h : i ≠ j) : Nat.Coprime (fnum i) (fnum j) := by
  wlog hij : i < j generalizing i j with H
  · exact (H (Ne.symm h) (by omega)).symm
  have h2 : 1 < 2 ^ (2 ^ j) := Nat.one_lt_two_pow (Nat.two_pow_pos j).ne'
  have hdvd : fnum i ∣ 2 ^ (2 ^ j) - 1 := fermat_dvd_nat i j hij
  have hval : fnum j = 2 ^ (2 ^ j) + 1 := rfl
  have hg2 : Nat.gcd (fnum i) (fnum j) ∣ 2 := by
    have h1 : Nat.gcd (fnum i) (fnum j) ∣ 2 ^ (2 ^ j) - 1 :=
      Nat.dvd_trans (Nat.gcd_dvd_left _ _) hdvd
    have h2' : Nat.gcd (fnum i) (fnum j) ∣ 2 ^ (2 ^ j) + 1 := by
      rw [← hval]; exact Nat.gcd_dvd_right _ _
    have h3 := Nat.dvd_sub h2' h1
    have h4 : 2 ^ (2 ^ j) + 1 - (2 ^ (2 ^ j) - 1) = 2 := by omega
    rwa [h4] at h3
  rw [Nat.coprime_iff_gcd_eq_one]
  have hgpos : 0 < Nat.gcd (fnum i) (fnum j) := Nat.gcd_pos_of_pos_left _ (by simp [fnum])
  have hle : Nat.gcd (fnum i) (fnum j) ≤ 2 := Nat.le_of_dvd (by norm_num) hg2
  have hne : Nat.gcd (fnum i) (fnum j) ≠ 2 := by
    intro hg
    have hd : 2 ∣ fnum i := hg ▸ Nat.gcd_dvd_left _ _
    have hodd := fermat_odd i
    omega
  omega

private abbrev ccls : List (ℕ × ℕ × ℕ) :=
  [(7, 3, 0), (73, 9, 7), (11, 10, 0), (13, 12, 5),
   (151, 15, 14), (19, 18, 1), (41, 20, 6), (241, 24, 11),
   (331, 30, 8), (37, 36, 13), (109, 36, 4), (61681, 40, 22),
   (631, 45, 19), (97, 48, 23), (673, 48, 47), (61, 60, 32),
   (1321, 60, 56), (433, 72, 31), (38737, 72, 67), (4278255361, 80, 2),
   (18837001, 90, 28), (4562284561, 120, 34), (181, 180, 172), (54001, 180, 136),
   (29247661, 180, 58), (394783681, 240, 122), (46908728641, 240, 202),
   (469775495062434961, 360, 94)]

private abbrev cprimes : List ℕ := ccls.map (fun t => t.1)

/-- `cmpe` is the product of the 28 covering primes. -/
private abbrev cmpe : ℕ := cprimes.prod

/-- `cres` is the simultaneous residue `2 ^ a_i mod p_i` and `-1 mod 16`. -/
private abbrev cres : ℕ := 26686573717487748862452387910863163349668306796366277254475249878721108356067403140878917528661124507160391837257813131023

private lemma covCheck :
    (List.range 720).all (fun r => ccls.any (fun t => r % t.2.1 == t.2.2)) = true := by
  decide +kernel

private lemma covDvd720 : ccls.all (fun t => decide (t.2.1 ∣ 720)) = true := by decide +kernel

private lemma covMod16 : ccls.all (fun t => decide (t.1 % 16 ≠ 15)) = true := by decide +kernel

private lemma covGt1 : ccls.all (fun t => decide (1 < t.1)) = true := by decide +kernel

private lemma covPow : ccls.all (fun t => decide (t.1 ∣ 2 ^ t.2.1 - 1)) = true := by
  decide +kernel

private lemma covCop : ccls.all (fun t => decide (Nat.Coprime t.1 65535)) = true := by
  decide +kernel

private lemma covR2 : ccls.all (fun t => decide (cres % t.1 = (2 ^ t.2.2) % t.1)) = true := by
  decide +kernel

private lemma covMp : ccls.all (fun t => decide (t.1 ∣ cmpe)) = true := by
  decide +kernel

private lemma r2_mod16 : cres % 16 = 15 := by decide

private lemma mp_le : 16 * cmpe ≤ cfac := by decide

private lemma fact_of_mem {P : ℕ × ℕ × ℕ → Bool} (h : ccls.all P = true) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ ccls) : P t = true := (List.all_eq_true.mp h) t ht

private lemma cov_dvd720 {t : ℕ × ℕ × ℕ} (ht : t ∈ ccls) : t.2.1 ∣ 720 :=
  of_decide_eq_true (fact_of_mem covDvd720 ht)

private lemma cov_mod16 {t : ℕ × ℕ × ℕ} (ht : t ∈ ccls) : t.1 % 16 ≠ 15 :=
  of_decide_eq_true (fact_of_mem covMod16 ht)

private lemma cov_gt1 {t : ℕ × ℕ × ℕ} (ht : t ∈ ccls) : 1 < t.1 :=
  of_decide_eq_true (fact_of_mem covGt1 ht)

private lemma cov_pow {t : ℕ × ℕ × ℕ} (ht : t ∈ ccls) : t.1 ∣ 2 ^ t.2.1 - 1 :=
  of_decide_eq_true (fact_of_mem covPow ht)

private lemma cov_cop {t : ℕ × ℕ × ℕ} (ht : t ∈ ccls) : Nat.Coprime t.1 65535 :=
  of_decide_eq_true (fact_of_mem covCop ht)

private lemma cov_r2 {t : ℕ × ℕ × ℕ} (ht : t ∈ ccls) : cres % t.1 = (2 ^ t.2.2) % t.1 :=
  of_decide_eq_true (fact_of_mem covR2 ht)

private lemma cov_mp {t : ℕ × ℕ × ℕ} (ht : t ∈ ccls) : t.1 ∣ cmpe :=
  of_decide_eq_true (fact_of_mem covMp ht)

/-- The covering property, transferred from `720` to a general exponent. -/
private lemma cov_exists (j : ℕ) : ∃ t ∈ ccls, j % t.2.1 = t.2.2 := by
  have h := covCheck
  simp only [List.all_eq_true, List.mem_range, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨t, ht, hjt⟩ := h (j % 720) (Nat.mod_lt _ (by norm_num))
  refine ⟨t, ht, ?_⟩
  rw [← hjt, Nat.mod_mod_of_dvd _ (cov_dvd720 ht)]


/-! ### Coprimality of the covering primes with `fprod N` -/

private lemma dvd_pow_gcd_sub_one {d a b : ℕ} (ha : d ∣ 2 ^ a - 1) (hb : d ∣ 2 ^ b - 1) :
    d ∣ 2 ^ (Nat.gcd a b) - 1 := by
  have key : ∀ {n : ℕ}, d ∣ 2 ^ n - 1 → (2 : ZMod d) ^ n = 1 := by
    intro n hn
    have h0 : ((2 ^ n - 1 : ℕ) : ZMod d) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact hn
    rw [Nat.cast_sub (Nat.one_le_two_pow)] at h0
    push_cast at h0
    exact sub_eq_zero.mp h0
  have h2 : (2 : ZMod d) ^ (Nat.gcd a b) = 1 := pow_gcd_eq_one.mpr ⟨key ha, key hb⟩
  have h3 : ((2 ^ Nat.gcd a b : ℕ) : ZMod d) = 1 := by push_cast; exact h2
  have h4 : ((2 ^ Nat.gcd a b - 1 : ℕ) : ZMod d) = 0 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow), h3]; simp
  rwa [ZMod.natCast_eq_zero_iff] at h4

private lemma pow_sub_one_dvd {a b : ℕ} (h : a ∣ b) : 2 ^ a - 1 ∣ 2 ^ b - 1 :=
  Nat.pow_sub_one_dvd_pow_sub_one 2 h

private lemma gcd720 (N : ℕ) (hN : 5 ≤ N) : Nat.gcd 720 (2 ^ N) = 16 := by
  have h16dvd : 16 ∣ 2 ^ N := by
    obtain ⟨k, hk⟩ : ∃ k, N = k + 4 := ⟨N - 4, by omega⟩
    rw [hk, pow_add]
    exact ⟨2 ^ k, by ring⟩
  have h16 : 16 ∣ Nat.gcd 720 (2 ^ N) := Nat.dvd_gcd (by norm_num) h16dvd
  obtain ⟨k, hk, hval⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_right 720 (2 ^ N))
  have hk720 : 2 ^ k ∣ 720 := hval ▸ Nat.gcd_dvd_left 720 (2 ^ N)
  have hd : 16 ∣ 2 ^ k := hval ▸ h16
  have hkle : k ≤ 4 := by
    have hle : 2 ^ k ≤ 720 := Nat.le_of_dvd (by norm_num) hk720
    have hk9 : k ≤ 9 := by
      by_contra h
      have h10 : 10 ≤ k := by omega
      have h1024 : 1024 ≤ 2 ^ k := by
        calc 1024 = 2 ^ 10 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h10
      omega
    interval_cases k <;> simp_all
  have hk4 : k = 4 := by
    interval_cases k <;> simp_all
  rw [hval, hk4]; norm_num

private lemma cfac_odd : cfac % 2 = 1 := gk_odd

private lemma cfac_dvd_fermat10 : cfac ∣ fnum 10 := ⟨cpk, by rw [mul_comm]; exact bk_gk⟩

private lemma cfac_dvd (N : ℕ) (hN : 11 ≤ N) : cfac ∣ 2 ^ (2 ^ N) - 1 :=
  dvd_trans cfac_dvd_fermat10 (by have := fermat_dvd_nat 10 N (by omega); simpa [fnum] using this)

private lemma fprod_spec (N : ℕ) (hN : 11 ≤ N) : cfac * fprod N = 2 ^ (2 ^ N) - 1 :=
  Nat.mul_div_cancel' (cfac_dvd N hN)

private lemma fprod_dvd (N : ℕ) (hN : 11 ≤ N) : fprod N ∣ 2 ^ (2 ^ N) - 1 :=
  ⟨cfac, by rw [mul_comm]; exact (fprod_spec N hN).symm⟩

private lemma fprod_odd (N : ℕ) (hN : 11 ≤ N) : fprod N % 2 = 1 := by
  have htwo : 2 ∣ 2 ^ (2 ^ N) := by
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ N = k + 1 := ⟨2 ^ N - 1, by have := Nat.two_pow_pos N; omega⟩
    rw [hk, pow_succ]
    exact ⟨2 ^ k, by ring⟩
  obtain ⟨c, hc⟩ := htwo
  have hc1 : 1 ≤ c := by
    have hge : 2 ≤ 2 ^ (2 ^ N) := by
      have := Nat.one_lt_two_pow (Nat.two_pow_pos N).ne'
      omega
    omega
  have h : (cfac * fprod N) % 2 = 1 := by
    rw [fprod_spec N hN, hc]
    omega
  rw [Nat.mul_mod, cfac_odd] at h
  simpa using h

private lemma coprime_fprod_of {p m N : ℕ} (hN : 11 ≤ N) (hm : m ∣ 720) (hp : p ∣ 2 ^ m - 1)
    (hc : Nat.Coprime p 65535) : Nat.Coprime p (fprod N) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  set d := Nat.gcd p (fprod N) with hd
  have hdp : d ∣ p := Nat.gcd_dvd_left _ _
  have hdF : d ∣ fprod N := Nat.gcd_dvd_right _ _
  have hd1 : d ∣ 2 ^ m - 1 := hdp.trans hp
  have hd2 : d ∣ 2 ^ (2 ^ N) - 1 := hdF.trans (fprod_dvd N hN)
  have hgcd16 : Nat.gcd m (2 ^ N) ∣ 16 := by
    have h1 : Nat.gcd m (2 ^ N) ∣ 720 := (Nat.gcd_dvd_left m (2 ^ N)).trans hm
    have h2 : Nat.gcd m (2 ^ N) ∣ 2 ^ N := Nat.gcd_dvd_right m (2 ^ N)
    have h3 := Nat.dvd_gcd h1 h2
    rwa [gcd720 N (by omega)] at h3
  have hd3 : d ∣ 2 ^ (Nat.gcd m (2 ^ N)) - 1 := dvd_pow_gcd_sub_one hd1 hd2
  have hd4 : d ∣ 2 ^ 16 - 1 := hd3.trans (pow_sub_one_dvd hgcd16)
  have hd5 : d ∣ Nat.gcd p 65535 := by
    refine Nat.dvd_gcd hdp ?_
    have : 2 ^ 16 - 1 = 65535 := by norm_num
    rwa [this] at hd4
  rw [hc] at hd5
  exact Nat.dvd_one.mp hd5

private lemma coprime_list_prod {L : List ℕ} {q : ℕ} (h : ∀ a ∈ L, Nat.Coprime a q) :
    Nat.Coprime L.prod q := by
  induction L with
  | nil => simpa using Nat.coprime_one_left q
  | cons a t ih =>
    rw [List.prod_cons]
    exact Nat.Coprime.mul_left (h a (List.mem_cons_self ..))
      (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

private lemma coprime_cmpe (N : ℕ) (hN : 11 ≤ N) : Nat.Coprime cmpe (fprod N) := by
  have hall : ∀ t ∈ ccls, Nat.Coprime t.1 (fprod N) := fun t ht =>
    coprime_fprod_of hN (cov_dvd720 ht) (cov_pow ht) (cov_cop ht)
  have : ∀ a ∈ cprimes, Nat.Coprime a (fprod N) := by
    intro a ha
    rw [cprimes, List.mem_map] at ha
    obtain ⟨t, ht, rfl⟩ := ha
    exact hall t ht
  exact coprime_list_prod this

private lemma coprime_16_fprod (N : ℕ) (hN : 11 ≤ N) : Nat.Coprime 16 (fprod N) := by
  have h2 : Nat.Coprime 2 (fprod N) := by
    rw [Nat.coprime_two_left]
    exact Nat.odd_iff.mpr (fprod_odd N hN)
  have := h2.pow_left 4
  simpa using this

private lemma coprime_crt (N : ℕ) (hN : 11 ≤ N) : Nat.Coprime (16 * cmpe) (fprod N) :=
  (coprime_16_fprod N hN).mul_left (coprime_cmpe N hN)


/-! ### The Fermat divisors `B_r` and their size and residue -/

private abbrev bterm (r : ℕ) : ℕ := if r = 10 then cpk else fnum r

private lemma bterm_gt1 (r : ℕ) : 1 < bterm r := by
  by_cases h : r = 10
  · subst h
    simp only [bterm, if_pos rfl, cpk]
    norm_num
  · simp only [bterm, if_neg h, fnum]
    have := Nat.two_pow_pos r
    have := Nat.one_le_two_pow (n := 2 ^ r)
    omega

private lemma bterm_dvd (r N : ℕ) (hN : 11 ≤ N) (hr : r < N) : bterm r ∣ fprod N := by
  by_cases h : r = 10
  · subst h
    have hf : fnum 10 ∣ 2 ^ (2 ^ N) - 1 := by
      have := fermat_dvd_nat 10 N (by omega)
      simpa [fnum] using this
    obtain ⟨R, hR⟩ := hf
    have hf10 : fnum 10 = cpk * cfac := by
      have h1 : fnum 10 = 2 ^ 1024 + 1 := by simp only [fnum]; norm_num
      rw [h1]; exact bk_gk.symm
    have hspec : fprod N = cpk * R := by
      show (2 ^ (2 ^ N) - 1) / cfac = cpk * R
      rw [hR, hf10]
      have hre : cpk * cfac * R = cfac * (cpk * R) := by ring
      rw [hre, Nat.mul_div_cancel_left _ (by have := gk_pos; omega : 0 < cfac)]
    simp only [bterm, if_pos rfl]
    exact ⟨R, hspec⟩
  · have hf : fnum r ∣ 2 ^ (2 ^ N) - 1 := by
      have := fermat_dvd_nat r N hr
      simpa [fnum] using this
    have hcop : Nat.Coprime (fnum r) cfac :=
      (fermat_coprime (by omega : r ≠ 10)).coprime_dvd_right cfac_dvd_fermat10
    have hf2 : fnum r ∣ fprod N * cfac := by
      rw [mul_comm, fprod_spec N hN]; exact hf
    have := hcop.dvd_of_dvd_mul_right hf2
    simp only [bterm, if_neg h]
    exact this

private lemma bterm_mod16 (r : ℕ) :
    bterm r % 16 = 1 ∨ bterm r % 16 = 3 ∨ bterm r % 16 = 5 := by
  by_cases h10 : r = 10
  · subst h10
    exact Or.inl (by decide)
  rcases Nat.lt_or_ge r 2 with h2 | h2
  · interval_cases r
    · exact Or.inr (Or.inl (by decide))
    · exact Or.inr (Or.inr (by decide))
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
    have hs : s + 2 ≠ 10 := by omega
    have h16 : 16 ∣ 2 ^ (2 ^ (s + 2)) := by
      have hsplit : 2 ^ (s + 2) = 4 * 2 ^ s := by rw [pow_add]; ring
      have h4 : 4 ≤ 2 ^ (s + 2) := by
        rw [hsplit]; exact Nat.le_mul_of_pos_right 4 (Nat.two_pow_pos s)
      have hp := Nat.pow_dvd_pow 2 h4
      simpa using hp
    obtain ⟨c, hc⟩ := h16
    have hb : bterm (s + 2) = 2 ^ (2 ^ (s + 2)) + 1 := by
      rw [bterm, if_neg hs, fnum]
    refine Or.inl ?_
    rw [hb, hc, Nat.add_mod, Nat.mul_mod]
    norm_num

private lemma cmpe_lt : cmpe < 2 ^ 402 := by decide

private lemma fprod_gt (N : ℕ) (hN : 11 ≤ N) : 2 ^ 900 < fprod N := by
  have hcl : 2 ^ 900 * cfac < 2 ^ 2000 := by
    have h1 : 2 ^ 900 * cfac < 2 ^ 900 * 2 ^ 1000 := by
      exact Nat.mul_lt_mul_of_pos_left gk_lt (by positivity)
    have h2 : 2 ^ 900 * 2 ^ 1000 = 2 ^ 1900 := by rw [← pow_add]
    rw [h2] at h1
    exact lt_trans h1 (Nat.pow_lt_pow_right (by norm_num) (by norm_num))
  have hbig : 2 ^ 2000 ≤ cfac * fprod N := by
    rw [fprod_spec N hN]
    have h1 : 2 ^ 11 ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
    norm_num at h1
    have h2 : 2 ^ 2000 < 2 ^ (2 ^ N) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have h3 : cfac * 2 ^ 900 < cfac * fprod N := by
    calc cfac * 2 ^ 900 = 2 ^ 900 * cfac := by ring
      _ < 2 ^ 2000 := hcl
      _ ≤ cfac * fprod N := hbig
  exact Nat.lt_of_mul_lt_mul_left h3

private lemma step16 {b c : ℕ}
    (hb : b % 16 = 1 ∨ b % 16 = 3 ∨ b % 16 = 5)
    (hc : c % 16 = 0 ∨ c % 16 = 2 ∨ c % 16 = 4 ∨ c % 16 = 8)
    (h : (b + c) % 16 = 15) : False := by
  rw [Nat.add_mod] at h
  rcases hb with h1 | h1 | h1 <;> rcases hc with h2 | h2 | h2 | h2 <;>
    rw [h1, h2] at h <;> norm_num at h


private lemma exists_pow_dvd_not (d : ℕ) (hd : 0 < d) :
    ∃ r, 2 ^ r ∣ d ∧ ¬ 2 ^ (r + 1) ∣ d := by
  have hex : ∃ s, ¬ 2 ^ (s + 1) ∣ d := by
    refine ⟨d, ?_⟩
    intro h
    have hle : 2 ^ (d + 1) ≤ d := Nat.le_of_dvd hd h
    have hlt : d < 2 ^ (d + 1) := by
      calc d < d + 1 := by omega
        _ < 2 ^ (d + 1) := Nat.lt_two_pow_self
    omega
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with hr | hr
  · rw [hr]; exact one_dvd d
  · have hlt : Nat.find hex - 1 < Nat.find hex := by omega
    have := Nat.find_min hex hlt
    have hsucc : Nat.find hex - 1 + 1 = Nat.find hex := Nat.succ_pred_eq_of_pos hr
    rwa [hsucc, not_not] at this

/-- The main construction: for each `N ≥ 11` an odd integer below `2 ^ (2 ^ N)` that is not a prime
plus two powers of two. -/
private lemma exists_mem (N : ℕ) (hN : 11 ≤ N) : ∃ n, n ∈ Erdos9A ∧ fprod N ≤ n := by
  classical
  set n : ℕ := (Nat.chineseRemainder (coprime_crt N hN) cres 0).1 with hndef
  have hres := (Nat.chineseRemainder (coprime_crt N hN) cres 0).2
  have hmod1 : n ≡ cres [MOD 16 * cmpe] := hres.1
  have hmod0 : n ≡ 0 [MOD fprod N] := hres.2
  have hfpos : 0 < fprod N := by
    have := fprod_gt N hN; omega
  have hcmpe0 : 16 * cmpe ≠ 0 := by
    have : 0 < cmpe := by decide
    omega
  have hlt : n < 16 * cmpe * fprod N :=
    Nat.chineseRemainder_lt_mul (coprime_crt N hN) cres 0 hcmpe0 (by omega)
  have hQn : fprod N ∣ n := Nat.modEq_zero_iff_dvd.mp hmod0
  have hn16 : n % 16 = 15 := (Nat.ModEq.of_dvd (show 16 ∣ 16 * cmpe from ⟨cmpe, rfl⟩) hmod1).trans
    (show cres ≡ 15 [MOD 16] from r2_mod16)
  have hcov : ∀ t ∈ ccls, n % t.1 = (2 ^ t.2.2) % t.1 := by
    intro t ht
    have h1 : n ≡ cres [MOD t.1] :=
      Nat.ModEq.of_dvd (Nat.dvd_trans (cov_mp ht) (dvd_mul_left cmpe 16)) hmod1
    exact h1.trans (cov_r2 ht)
  have hnlt : n < 2 ^ (2 ^ N) - 1 := by
    have h1 : 16 * cmpe * fprod N ≤ cfac * fprod N :=
      Nat.mul_le_mul_right _ mp_le
    have h2 : cfac * fprod N = 2 ^ (2 ^ N) - 1 := fprod_spec N hN
    omega
  have hnpos : 0 < n := by omega
  have hnge : fprod N ≤ n := Nat.le_of_dvd hnpos hQn
  have hgn : 2 ^ 900 < n := lt_of_lt_of_le (fprod_gt N hN) hnge
  refine ⟨n, ⟨Nat.odd_iff.mpr (by omega), ?_⟩, hnge⟩
  rintro ⟨p, k, l, hp, hnk⟩
  -- the covering system kills every representation as a prime plus one power of two
  have sp : ∀ j : ℕ, 1 ≤ j → n = p + 2 ^ j → False := by
    intro j hj hjn
    obtain ⟨t, ht, hmod⟩ := cov_exists j
    have hdvdm : t.1 ∣ 2 ^ t.2.1 - 1 := cov_pow ht
    have hd1 : 1 < t.1 := cov_gt1 ht
    have hm1 : 2 ^ t.2.1 % t.1 = 1 := by
      have h0 : (2 ^ t.2.1 - 1) % t.1 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvdm
      have hsucc : 2 ^ t.2.1 - 1 + 1 = 2 ^ t.2.1 := Nat.succ_pred_eq_of_pos (Nat.two_pow_pos _)
      rw [← hsucc, Nat.add_mod, h0, Nat.zero_add, Nat.mod_eq_of_lt hd1, Nat.mod_eq_of_lt hd1]
    have hpow : 2 ^ j % t.1 = 2 ^ t.2.2 % t.1 := by
      obtain ⟨q, hq⟩ : ∃ q, j = t.2.1 * q + t.2.2 := by
        refine ⟨j / t.2.1, ?_⟩
        have hh : t.2.1 * (j / t.2.1) + j % t.2.1 = j := Nat.div_add_mod j t.2.1
        rw [hmod] at hh
        omega
      rw [hq, pow_add, pow_mul]
      have hq1 : (2 ^ t.2.1) ^ q % t.1 = 1 := by
        rw [Nat.pow_mod, hm1, one_pow, Nat.mod_eq_of_lt hd1]
      rw [Nat.mul_mod, hq1]
      norm_num
    have hme : n ≡ 2 ^ j [MOD t.1] := by
      show n % t.1 = 2 ^ j % t.1
      rw [hcov t ht, hpow]
    have hp2 := hp.two_le
    have h2jle : 2 ^ j ≤ n := by omega
    have hsub : (n - 2 ^ j) ≡ 0 [MOD t.1] := by
      have h2 := Nat.ModEq.sub h2jle (le_refl (2 ^ j)) hme (Nat.ModEq.refl (n := t.1) (2 ^ j))
      simpa using h2
    have hpdvd : t.1 ∣ p := by
      rw [show p = n - 2 ^ j by omega]
      exact Nat.modEq_zero_iff_dvd.mp hsub
    have hpt : p = t.1 := (hp.dvd_iff_eq (by omega)).mp hpdvd
    rcases Nat.lt_or_ge j 4 with hj4 | hj4
    · have hp402 : p < 2 ^ 402 := by
        rw [hpt]
        exact lt_of_le_of_lt (Nat.le_of_dvd (by omega) (cov_mp ht)) cmpe_lt
      have hsmall : 2 ^ j ≤ 8 := by
        calc 2 ^ j ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 8 := by norm_num
      have hmid : 2 ^ 402 + 8 < 2 ^ 900 := by norm_num
      have hbig : 2 ^ 900 < p + 2 ^ j := by rw [← hjn]; exact hgn
      omega
    · have h16 : 16 ∣ 2 ^ j := by
        have := Nat.pow_dvd_pow 2 (show 4 ≤ j from hj4)
        simpa using this
      have hp16 : p % 16 = 15 := by
        have h2 : (p + 2 ^ j) % 16 = 15 := by rw [← hjn]; exact hn16
        have hza : 2 ^ j ≡ 0 [MOD 16] := Nat.dvd_iff_mod_eq_zero.mp h16
        have hm : p + 2 ^ j ≡ p [MOD 16] := by
          have s1 := (Nat.ModEq.refl (n := 16) p).add hza
          simpa using s1
        rw [hm] at h2
        exact h2
      rw [hpt] at hp16
      exact cov_mod16 ht hp16
  -- a prime plus two distinct powers of two is killed by the Fermat divisors
  have key : ∀ a b : ℕ, 1 ≤ b → b < a → n = p + 2 ^ a + 2 ^ b → False := by
    intro a b hb hba hna
    have hp2 := hp.two_le
    have hd : 0 < a - b := by omega
    obtain ⟨r, hr1, hr2⟩ := exists_pow_dvd_not (a - b) hd
    obtain ⟨t, ht⟩ : ∃ t, a - b = 2 ^ r * t := hr1
    have hdvdab : 2 ^ r ∣ a - b := ⟨t, ht⟩
    have htodd : Odd t := by
      rcases Nat.even_or_odd t with he | ho
      · exfalso
        obtain ⟨u, hu⟩ := he
        apply hr2
        refine ⟨u, ?_⟩
        rw [ht, hu, pow_succ]
        ring
      · exact ho
    have hdvdF : fnum r ∣ 2 ^ (a - b) + 1 := by
      have h1 : 2 ^ (2 ^ r) + 1 ∣ (2 ^ (2 ^ r)) ^ t + 1 ^ t :=
        Odd.nat_add_dvd_pow_add_pow (x := 2 ^ (2 ^ r)) (y := 1) htodd
      have h2 : (2 ^ (2 ^ r)) ^ t = 2 ^ (a - b) := by rw [← pow_mul, ← ht]
      simpa [fnum, h2] using h1
    have hbk : bterm r ∣ 2 ^ (a - b) + 1 := by
      by_cases h10 : r = 10
      · have hfk : fnum 10 = cpk * cfac := by
          have h1 : fnum 10 = 2 ^ 1024 + 1 := by simp only [fnum]; norm_num
          rw [h1]; exact bk_gk.symm
        have hc1 : cpk ∣ fnum 10 := by rw [hfk]; exact dvd_mul_right _ _
        rw [bterm, if_pos h10]
        exact (h10 ▸ hc1).trans hdvdF
      · rw [bterm, if_neg h10]; exact hdvdF
    have hak : a < 2 ^ N := by
      have h2 : 2 ^ a < n := by
        rw [hna]
        have heq : p + 2 ^ a + 2 ^ b = (p + 2 ^ b) + 2 ^ a := by ring
        rw [heq]
        exact Nat.lt_add_of_pos_left (by positivity)
      have h3 : n < 2 ^ (2 ^ N) := by omega
      have h4 : 2 ^ a < 2 ^ (2 ^ N) := lt_trans h2 h3
      by_contra hcon
      have h5 : 2 ^ N ≤ a := by omega
      have h6 : 2 ^ (2 ^ N) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) h5
      omega
    have hrN : r < N := by
      have hle : 2 ^ r ≤ a - b := Nat.le_of_dvd hd hdvdab
      have hlt2 : 2 ^ r < 2 ^ N := by omega
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    have hdvdQ : bterm r ∣ fprod N := bterm_dvd r N hN hrN
    have hsumab : 2 ^ a + 2 ^ b = 2 ^ b * (2 ^ (a - b) + 1) := by
      rw [mul_add, mul_one, ← pow_add, Nat.add_sub_cancel' hba.le]
    have h1 : bterm r ∣ 2 ^ a + 2 ^ b := by
      rw [hsumab]; exact dvd_mul_of_dvd_right hbk _
    have hdvdp : bterm r ∣ p := by
      have h3 : bterm r ∣ n := hdvdQ.trans hQn
      have hp' : p = n - (2 ^ a + 2 ^ b) := by omega
      rw [hp']
      exact Nat.dvd_sub h3 h1
    have hbterm : p = bterm r := (hp.dvd_iff_eq (by have := bterm_gt1 r; omega)).mp hdvdp
    have hb16 := bterm_mod16 r
    have hgb : 1 < bterm r := bterm_gt1 r
    rcases Nat.lt_or_ge a 4 with ha4 | ha4
    · have ha8 : 2 ^ a ≤ 8 := by
        calc 2 ^ a ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 8 := by norm_num
      have hb8 : 2 ^ b ≤ 8 := by
        calc 2 ^ b ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ 8 := ha8
      have hs : 2 ^ a + 2 ^ b ≤ 16 := by
        calc 2 ^ a + 2 ^ b ≤ 8 + 8 := add_le_add ha8 hb8
          _ = 16 := by norm_num
      have hle16 : p ≤ 16 := by
        calc p = bterm r := hbterm
          _ ≤ 2 ^ a + 2 ^ b := Nat.le_of_dvd (by omega) h1
          _ ≤ 16 := hs
      have hn32 : n ≤ 32 := by
        calc n = p + (2 ^ a + 2 ^ b) := by rw [hna]; ring
          _ ≤ 16 + 16 := add_le_add hle16 hs
          _ = 32 := by norm_num
      omega
    · have h16 : 16 ∣ 2 ^ a := by
        have := Nat.pow_dvd_pow 2 (show 4 ≤ a from ha4)
        simpa using this
      have hc16 : 2 ^ b % 16 = 0 ∨ 2 ^ b % 16 = 2 ∨ 2 ^ b % 16 = 4 ∨ 2 ^ b % 16 = 8 := by
        rcases Nat.lt_or_ge b 4 with h | h
        · interval_cases b <;> decide
        · left
          exact Nat.dvd_iff_mod_eq_zero.mp (by
            have := Nat.pow_dvd_pow 2 h; simpa using this)
      have hsum : (bterm r + 2 ^ b) % 16 = 15 := by
        have h1' : n = bterm r + 2 ^ a + 2 ^ b := by rw [← hbterm]; omega
        have h2 : (bterm r + 2 ^ a + 2 ^ b) % 16 = 15 := by rw [← h1']; exact hn16
        have hza : 2 ^ a ≡ 0 [MOD 16] := Nat.dvd_iff_mod_eq_zero.mp h16
        have hm : bterm r + 2 ^ a + 2 ^ b ≡ bterm r + 2 ^ b [MOD 16] := by
          have s1 : bterm r + 2 ^ a ≡ bterm r + 0 [MOD 16] :=
            (Nat.ModEq.refl (n := 16) (bterm r)).add hza
          have s2 := s1.add (Nat.ModEq.refl (n := 16) (2 ^ b))
          simpa using s2
        rw [hm] at h2
        exact h2
      exact step16 hb16 hc16 hsum
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rcases Nat.eq_zero_or_pos l with hl | hl
    · refine sp 1 (by norm_num) ?_
      rw [hnk, hk, hl]
      norm_num
    · rcases hp.eq_two_or_odd' with hp2 | hpodd
      · subst hp2
        have h3 : n % 16 = (3 + 2 ^ l) % 16 := by
          rw [hnk, hk]
          norm_num
        have h2l : 2 ^ l % 16 = 0 ∨ 2 ^ l % 16 = 2 ∨ 2 ^ l % 16 = 4 ∨ 2 ^ l % 16 = 8 := by
          rcases Nat.lt_or_ge l 4 with h | h
          · interval_cases l <;> decide
          · left
            exact Nat.dvd_iff_mod_eq_zero.mp (by
              have := Nat.pow_dvd_pow 2 h; simpa using this)
        rw [h3, Nat.add_mod] at hn16
        rcases h2l with h | h | h | h <;> rw [h] at hn16 <;> norm_num at hn16
      · obtain ⟨a, ha⟩ := hpodd
        obtain ⟨c, hc⟩ : ∃ c, 2 ^ l = c + c := by
          obtain ⟨d, rfl⟩ : ∃ d, l = d + 1 := ⟨l - 1, (Nat.sub_add_cancel hl).symm⟩
          exact ⟨2 ^ d, by rw [pow_succ]; ring⟩
        have heven : Even n := ⟨a + c + 1, by rw [hnk, hk, ha, hc]; ring⟩
        have hev : n % 2 = 0 := Nat.even_iff.mp heven
        have hodd : n % 2 = 1 :=
          Nat.ModEq.of_dvd (show 2 ∣ 16 from ⟨8, rfl⟩) (show n ≡ 15 [MOD 16] from hn16)
        rw [hev] at hodd
        exact Nat.zero_ne_one hodd
  · rcases Nat.eq_zero_or_pos l with hl | hl
    · rcases hp.eq_two_or_odd' with hp2 | hpodd
      · subst hp2
        have h3 : n % 16 = (3 + 2 ^ k) % 16 := by
          rw [hnk, hl]
          congr 1
          ring
        have h2l : 2 ^ k % 16 = 0 ∨ 2 ^ k % 16 = 2 ∨ 2 ^ k % 16 = 4 ∨ 2 ^ k % 16 = 8 := by
          rcases Nat.lt_or_ge k 4 with h | h
          · interval_cases k <;> decide
          · left
            exact Nat.dvd_iff_mod_eq_zero.mp (by
              have := Nat.pow_dvd_pow 2 h; simpa using this)
        rw [h3, Nat.add_mod] at hn16
        rcases h2l with h | h | h | h <;> rw [h] at hn16 <;> norm_num at hn16
      · obtain ⟨a, ha⟩ := hpodd
        obtain ⟨c, hc⟩ : ∃ c, 2 ^ k = c + c := by
          obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩
          exact ⟨2 ^ d, by rw [pow_succ]; ring⟩
        have heven : Even n := ⟨a + c + 1, by rw [hnk, hl, ha, hc]; ring⟩
        have hev : n % 2 = 0 := Nat.even_iff.mp heven
        have hodd : n % 2 = 1 :=
          Nat.ModEq.of_dvd (show 2 ∣ 16 from ⟨8, rfl⟩) (show n ≡ 15 [MOD 16] from hn16)
        rw [hev] at hodd
        exact Nat.zero_ne_one hodd
    · rcases eq_or_ne k l with hkl | hkl
      · refine sp (k + 1) (by omega) ?_
        rw [hnk, ← hkl]
        have h2 : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
          rw [← two_mul, ← pow_succ']
        rw [show p + 2 ^ k + 2 ^ k = p + (2 ^ k + 2 ^ k) by ring, h2]
      · rcases Nat.lt_or_gt_of_ne hkl with hlt | hlt
        · exact key l k hk hlt (by rw [hnk]; ring)
        · exact key k l hl hlt hnk

private lemma fprod_ge (N : ℕ) (hN : 11 ≤ N) : 2 ^ (2 ^ N - 1001) ≤ fprod N := by
  have hspec : cfac * fprod N = 2 ^ (2 ^ N) - 1 := fprod_spec N hN
  have h2N : 1001 ≤ 2 ^ N := by
    have h5 : 2 ^ 11 ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
    norm_num at h5
    omega
  have hfac : 2 ^ (2 ^ N - 1001) * 2 ^ 1000 = 2 ^ (2 ^ N - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have h1 : 2 ^ (2 ^ N - 1001) * cfac < 2 ^ (2 ^ N - 1001) * 2 ^ 1000 :=
    Nat.mul_lt_mul_of_pos_left gk_lt (by positivity)
  rw [hfac] at h1
  have h3 : 2 ^ (2 ^ N - 1) < 2 ^ (2 ^ N) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ (2 ^ N - 1001) * cfac < 2 ^ (2 ^ N) - 1 := by omega
  have h5 : 2 ^ (2 ^ N - 1001) * cfac < fprod N * cfac := by
    rw [mul_comm (fprod N), hspec]
    exact h4
  exact Nat.le_of_mul_le_mul_right (le_of_lt h5) (by positivity)


/-- Unit U-1603, route lemma, PROVED, a Lean proof of a KNOWN result. Plain math: infinitely many
odd numbers are not a prime plus two powers of 2. Credit, read 2026-11-05: erdosproblems.com/9 gives
Crocker [Cr71] with `≫ log log N` such integers up to `N`, and Pan [Pa11] with `≫_ε N^(1-ε)`. Its
copies disagree on Schinzel: the problem page says Erdős [Er77c] credits Schinzel, with no
reference, and the page text served at /latex/9 does not name him. The FC page repeats the Erdős
credit. [Cr71] and [Pa11] were not read here. FC tags it solved with an outside Lean proof whose
body module was not read here. A first step of Erdős 9, far weaker than positive upper density. -/
theorem route_erdos9A_infinite : Erdos9A.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro B
  have hN : 11 ≤ B + 2000 := by omega
  obtain ⟨n, hnA, hnge⟩ := exists_mem (B + 2000) hN
  refine ⟨n, hnA, ?_⟩
  have h1 : 2 ^ (2 ^ (B + 2000) - 1001) ≤ fprod (B + 2000) := fprod_ge _ hN
  have h2 : B < 2 ^ (2 ^ (B + 2000) - 1001) := by
    have h7 : B + 1002 ≤ 2 ^ (B + 2000) := by
      have h8 : B + 2000 < 2 ^ (B + 2000) := Nat.lt_two_pow_self
      omega
    have h8 : (B + 1002) - 1001 ≤ 2 ^ (B + 2000) - 1001 := Nat.sub_le_sub_right h7 1001
    have h9 : (B + 1002) - 1001 = B + 1 := by omega
    have hX : B + 1 ≤ 2 ^ (B + 2000) - 1001 := h9 ▸ h8
    calc B < 2 ^ B := Nat.lt_two_pow_self
      _ ≤ 2 ^ (B + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 2 ^ (2 ^ (B + 2000) - 1001) := Nat.pow_le_pow_right (by norm_num) hX
  calc B < 2 ^ (2 ^ (B + 2000) - 1001) := h2
    _ ≤ fprod (B + 2000) := h1
    _ ≤ n := hnge



section

open Finset Real
open LeanLab.BrunGap LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

/-! ### Support for `route_lemoine_positive_density`

The mean square bound `S2` of `SchnirelmannGoldbach/S2.lean` (`∑ singProd n ^ 2 ≤ C N`) is copied
privately, `gapUpper` is restated with its constant made explicit so that it is uniform in the gap,
and the representation count `repCnt n` of `n = p + 2 q` is bounded below and in mean square. -/
/-! ### Copied from `SchnirelmannGoldbach/S2.lean`: the mean square of the singular product -/

/-- `singProd n ≤ σ(n)/n`. -/
private lemma singProd_le_sum_divisors (n : ℕ) (hn : n ≠ 0) :
    singProd n ≤ ∑ d ∈ n.divisors, 1 / (d : ℝ) := by
  classical
  unfold singProd
  have h1 : ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)) =
      ∑ t ∈ n.primeFactors.powerset, 1 / (((∏ p ∈ t, p : ℕ)) : ℝ) := by
    rw [show (∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ))) =
        ∏ p ∈ n.primeFactors, (1 / (p : ℝ) + 1) by simp [add_comm], Finset.prod_add]
    apply Finset.sum_congr rfl
    intro t _
    simp [Finset.prod_inv_distrib]
  rw [h1]
  have hinj : Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) (n.primeFactors.powerset : Set (Finset ℕ)) := by
    intro t ht t' ht' h
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at ht ht'
    have e1 := Nat.primeFactors_prod (s := t) (fun p hp => Nat.prime_of_mem_primeFactors (ht hp))
    have e2 := Nat.primeFactors_prod (s := t') (fun p hp => Nat.prime_of_mem_primeFactors (ht' hp))
    simp only at h
    rw [← e1, ← e2, h]
  rw [← Finset.sum_image (f := fun d : ℕ => 1 / (d : ℝ)) hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    simp only [mem_image, mem_powerset] at hd
    obtain ⟨t, ht, rfl⟩ := hd
    rw [Nat.mem_divisors]
    exact ⟨(Finset.prod_dvd_prod_of_subset _ _ id ht).trans (Nat.prod_primeFactors_dvd n), hn⟩
  · intro _ _ _; positivity

/-- weight `1/(d √d)`. -/
private noncomputable def wt (d : ℕ) : ℝ := 1 / ((d : ℝ) * √(d : ℝ))

private lemma wt_nonneg (d : ℕ) : 0 ≤ wt d := by unfold wt; positivity

private lemma wt_summable : Summable wt := by
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  refine Summable.of_nonneg_of_le wt_nonneg (fun d => ?_) hs
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [wt]
  · have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have : (d : ℝ) ^ ((3 : ℝ) / 2) = (d : ℝ) * √(d : ℝ) := by
      rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hd',
        Real.rpow_one]
    rw [this, wt, one_div]

private lemma card_dvd_route (N d : ℕ) : (#{n ∈ Icc 1 N | d ∣ n} : ℝ) ≤ N / d := by
  have : (Icc 1 N) = Ioc 0 N := rfl
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]
  exact Nat.cast_div_le

private lemma pair_le_aux (N d1 d2 : ℕ) (h1 : 1 ≤ d1) :
    ∑ n ∈ Icc 1 N, (if d1 ∣ n then 1 / (d1 : ℝ) else 0) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0)
      ≤ N / ((d1 : ℝ) * d2 * d2) := by
  have hd1 : (0 : ℝ) < d1 := by exact_mod_cast h1
  calc ∑ n ∈ Icc 1 N, (if d1 ∣ n then 1 / (d1 : ℝ) else 0) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0)
      ≤ ∑ n ∈ Icc 1 N, 1 / (d1 : ℝ) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0) := by
        apply Finset.sum_le_sum; intro n _
        apply mul_le_mul_of_nonneg_right
        · split_ifs
          · exact le_rfl
          · positivity
        · split_ifs <;> positivity
    _ = 1 / (d1 : ℝ) * (1 / d2) * #{n ∈ Icc 1 N | d2 ∣ n} := by
        rw [← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
          nsmul_eq_mul]; ring
    _ ≤ 1 / (d1 : ℝ) * (1 / d2) * (N / d2) := by
        gcongr; exact card_dvd_route N d2
    _ = N / ((d1 : ℝ) * d2 * d2) := by field_simp

private lemma wt_mul_bound (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (1 : ℝ) / (a * b * b) ≤ wt a * wt b := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hb' : (1 : ℝ) ≤ b := ha'.trans hab'
  unfold wt
  rw [div_mul_div_comm, one_mul]
  apply one_div_le_one_div_of_le
  · have : 0 < √(a : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have : 0 < √(b : ℝ) := Real.sqrt_pos.mpr (by linarith)
    positivity
  · have hs : √(a : ℝ) ≤ √(b : ℝ) := Real.sqrt_le_sqrt hab'
    have hbb : √(b : ℝ) * √(b : ℝ) = b := Real.mul_self_sqrt (by linarith)
    have h0 : 0 ≤ √(b : ℝ) := Real.sqrt_nonneg _
    have hab0 : (0 : ℝ) ≤ a * b := by positivity
    calc (a : ℝ) * √a * (b * √b) = a * b * (√a * √b) := by ring
      _ ≤ a * b * (√b * √b) := by gcongr
      _ = a * b * b := by rw [hbb]

private lemma pair_le (N d1 d2 : ℕ) (h1 : 1 ≤ d1) (h2 : 1 ≤ d2) :
    ∑ n ∈ Icc 1 N, (if d1 ∣ n then 1 / (d1 : ℝ) else 0) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0)
      ≤ N * (wt d1 * wt d2) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  rcases le_total d1 d2 with h | h
  · refine (pair_le_aux N d1 d2 h1).trans ?_
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (wt_mul_bound d1 d2 h1 h) hN
  · have := pair_le_aux N d2 d1 h2
    simp_rw [mul_comm (if d2 ∣ _ then _ else _)] at this
    refine this.trans ?_
    rw [div_eq_mul_one_div, mul_comm (wt d1)]
    exact mul_le_mul_of_nonneg_left (wt_mul_bound d2 d1 h2 h) hN

private theorem S2_holds_route : S2 := by
  refine ⟨(∑' d, wt d) ^ 2, fun N _ => ?_⟩
  have key : ∀ n ∈ Icc 1 N, singProd n ^ 2 ≤
      ∑ d1 ∈ Icc 1 N, ∑ d2 ∈ Icc 1 N,
        (if d1 ∣ n then 1 / (d1 : ℝ) else 0) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0) := by
    intro n hn
    rw [mem_Icc] at hn
    have hsum : ∑ d ∈ n.divisors, 1 / (d : ℝ) =
        ∑ d ∈ Icc 1 N, (if d ∣ n then 1 / (d : ℝ) else 0) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext d
      simp only [Nat.mem_divisors, mem_filter, mem_Icc]
      constructor
      · rintro ⟨hd, -⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), (Nat.le_of_dvd (by omega) hd).trans hn.2⟩, hd⟩
      · rintro ⟨-, hd⟩; exact ⟨hd, by omega⟩
    rw [← Finset.sum_mul_sum, ← sq, ← hsum]
    gcongr
    · exact singProd_nonneg n
    · exact singProd_le_sum_divisors n (by omega)
  calc ∑ n ∈ Icc 1 N, singProd n ^ 2
      ≤ ∑ n ∈ Icc 1 N, ∑ d1 ∈ Icc 1 N, ∑ d2 ∈ Icc 1 N,
        (if d1 ∣ n then 1 / (d1 : ℝ) else 0) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0) :=
        Finset.sum_le_sum key
    _ = ∑ d1 ∈ Icc 1 N, ∑ d2 ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (if d1 ∣ n then 1 / (d1 : ℝ) else 0) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0) := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro _ _; rw [Finset.sum_comm]
    _ ≤ ∑ d1 ∈ Icc 1 N, ∑ d2 ∈ Icc 1 N, (N : ℝ) * (wt d1 * wt d2) := by
        apply Finset.sum_le_sum; intro d1 hd1; apply Finset.sum_le_sum; intro d2 hd2
        exact pair_le N d1 d2 (mem_Icc.mp hd1).1 (mem_Icc.mp hd2).1
    _ = N * (∑ d ∈ Icc 1 N, wt d) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro _ _; rw [Finset.mul_sum]
    _ ≤ N * (∑' d, wt d) ^ 2 := by
        gcongr
        · exact Finset.sum_nonneg (fun d _ => wt_nonneg d)
        · exact wt_summable.sum_le_tsum _ (fun d _ => wt_nonneg d)
    _ = (∑' d, wt d) ^ 2 * N := by ring

/-! ### `gapUpper` with its constant made explicit, uniform in the gap -/

/-- Brun's upper bound for prime pairs at an even gap, with the explicit constant of
`BrunGap.gapUpper` (whose proof is copied here so that the constant does not depend on the gap). -/
private theorem gapUniform (h N : ℕ) (hh : Even h) (hh0 : h ≠ 0) (hN : 3 ≤ N) :
    (gapCount h N : ℝ) ≤ (128 + 5 * 17 ^ 8) * singProd h * N / Real.log N ^ 2 := by
  have hN1 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hsp := one_le_singProd h
  set S := singProd h
  set z := √(N : ℝ) with hz
  have hz1 : 1 < z := by
    rw [hz, Real.lt_sqrt (by norm_num)]; linarith
  have hb := gapCount_le h N hh hh0 hz1
  have hlogz : Real.log z = Real.log N / 2 := Real.log_sqrt (by positivity)
  have hlogz0 : 0 ≤ Real.log z := Real.log_nonneg hz1.le
  have hmain : 32 * (N : ℝ) * S / Real.log z ^ 2 = 128 * S * N / Real.log N ^ 2 := by
    rw [hlogz]; field_simp; ring
  have hlz : Real.log z ≤ Real.log N := by rw [hlogz]; linarith
  have hpow1 : 1 ≤ (1 + Real.log z) ^ 6 := one_le_pow₀ (by linarith)
  have herr1 : z * (1 + Real.log z) ^ 6 + (z + 1) ≤ 5 * (z * (1 + Real.log N) ^ 6) := by
    have : (1 + Real.log z) ^ 6 ≤ (1 + Real.log N) ^ 6 := by gcongr
    nlinarith
  have hpb := polylog_bound N (by linarith)
  have herr2 : z * (1 + Real.log N) ^ 6 ≤ 17 ^ 8 * N / Real.log N ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have herr3 : (17 : ℝ) ^ 8 * N / Real.log N ^ 2 ≤ 17 ^ 8 * S * N / Real.log N ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : (0 : ℝ) ≤ 17 ^ 8 * N := by positivity
    nlinarith
  have : (128 + 5 * 17 ^ 8 : ℝ) * S * N / Real.log N ^ 2 =
      128 * S * N / Real.log N ^ 2 + 5 * (17 ^ 8 * S * N / Real.log N ^ 2) := by ring
  rw [this]
  linarith
/-! ### The representation count `n = p + 2 q` -/

/-- `repSet n` is the set of primes `q` with `n - 2 q` prime, i.e. of the representations
`n = (n - 2 q) + 2 q`. -/
private def repSet (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun q => q.Prime ∧ (n - 2 * q).Prime)

/-- The number of representations `n = p + 2 q`. -/
private def repCnt (n : ℕ) : ℕ := (repSet n).card

private lemma isLemoine_of_repCnt_pos {n : ℕ} (h : 0 < repCnt n) : IsLemoine n := by
  obtain ⟨q, hq⟩ := card_pos.mp h
  simp only [repSet, mem_filter, mem_range] at hq
  obtain ⟨-, hqP, hq2P⟩ := hq
  exact ⟨n - 2 * q, q, hq2P, hqP, by have := hq2P.two_le; omega⟩

private lemma primeCounting_eq_card (m : ℕ) :
    Nat.primeCounting m = #(Nat.primesBelow (m + 1)) := by
  rw [Nat.primesBelow_card_eq_primeCounting']; rfl

private lemma primesBelow_eq (m : ℕ) : Nat.primesBelow m = (range m).filter Nat.Prime := rfl

/-- First moment: the odd primes `p ≤ N / 2` and the primes `q ≤ N / 4` give distinct
representations of odd numbers `p + 2 q ≤ N`. -/
private lemma first_moment (N : ℕ) (hN : 8 ≤ N) :
    (Nat.primeCounting (N / 2) - 1) * Nat.primeCounting (N / 4) ≤
      ∑ n ∈ (Icc 1 N).filter Odd, repCnt n := by
  classical
  set Pp := ((range (N / 2 + 1)).filter Nat.Prime).erase 2 with hPp
  set Qq := (range (N / 4 + 1)).filter Nat.Prime with hQq
  have h2mem : 2 ∈ (range (N / 2 + 1)).filter Nat.Prime := by
    rw [mem_filter, mem_range]
    exact ⟨by omega, Nat.prime_two⟩
  have hPcard : Pp.card = Nat.primeCounting (N / 2) - 1 := by
    rw [hPp, card_erase_of_mem h2mem, primeCounting_eq_card, primesBelow_eq]
  have hQcard : Qq.card = Nat.primeCounting (N / 4) := by
    rw [hQq, primeCounting_eq_card, primesBelow_eq]
  have hmaps : ∀ pq ∈ Pp ×ˢ Qq,
      (⟨pq.1 + 2 * pq.2, pq.2⟩ : Sigma fun n => ℕ) ∈
        ((Icc 1 N).filter Odd).sigma (fun n => repSet n) := by
    intro pq hpq
    simp only [mem_product] at hpq
    obtain ⟨hp, hq⟩ := hpq
    rw [hPp] at hp
    rw [hQq] at hq
    simp only [mem_erase, mem_filter, mem_range] at hp hq
    obtain ⟨hpne, hpLt, hpP⟩ := hp
    obtain ⟨hqLt, hqP⟩ := hq
    rw [mem_sigma, mem_filter, mem_Icc, repSet, mem_filter, mem_range]
    dsimp only
    have hp2 : 2 ≤ pq.1 := hpP.two_le
    have hq2 : 2 ≤ pq.2 := hqP.two_le
    have hpodd : Odd pq.1 := hpP.odd_of_ne_two hpne
    obtain ⟨k, hk⟩ := hpodd
    refine ⟨⟨⟨by omega, by omega⟩, ⟨k + pq.2, by omega⟩⟩, by omega, hqP, ?_⟩
    have : pq.1 + 2 * pq.2 - 2 * pq.2 = pq.1 := by omega
    rw [this]
    exact hpP
  have hinj : Set.InjOn (fun pq : ℕ × ℕ => (⟨pq.1 + 2 * pq.2, pq.2⟩ : Sigma fun n => ℕ))
      ↑(Pp ×ˢ Qq) := by
    intro a _ b _ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h2' : a.2 = b.2 := by simpa using h2
    ext
    · omega
    · exact h2'
  have hcard := card_le_card_of_injOn
    (fun pq : ℕ × ℕ => (⟨pq.1 + 2 * pq.2, pq.2⟩ : Sigma fun n => ℕ)) hmaps hinj
  rw [← hPcard, ← hQcard]
  calc Pp.card * Qq.card = #(Pp ×ˢ Qq) := (card_product _ _).symm
    _ ≤ #(((Icc 1 N).filter Odd).sigma (fun n => repSet n)) := hcard
    _ = ∑ n ∈ (Icc 1 N).filter Odd, repCnt n := by rw [card_sigma]; rfl

/-! ### Second moment -/

private lemma repSet_facts {n q : ℕ} (h : q ∈ repSet n) :
    q.Prime ∧ (n - 2 * q).Prime ∧ 2 * q + 2 ≤ n := by
  simp only [repSet, mem_filter, mem_range] at h
  exact ⟨h.2.1, h.2.2, by have := h.2.2.two_le; omega⟩

private lemma mem_total_facts {N : ℕ} {x : Sigma fun n => ℕ × ℕ}
    (h : x ∈ ((Icc 1 N).filter Odd).sigma (fun n => repSet n ×ˢ repSet n)) :
    x.1 ≤ N ∧ 2 * x.2.1 + 2 ≤ x.1 ∧ 2 * x.2.2 + 2 ≤ x.1 ∧
      x.2.1.Prime ∧ x.2.2.Prime ∧ (x.1 - 2 * x.2.1).Prime ∧ (x.1 - 2 * x.2.2).Prime := by
  simp only [mem_sigma, mem_product, mem_filter, mem_Icc] at h
  obtain ⟨⟨⟨-, hN⟩, -⟩, h1, h2⟩ := h
  obtain ⟨h1P, h1s, h1b⟩ := repSet_facts h1
  obtain ⟨h2P, h2s, h2b⟩ := repSet_facts h2
  exact ⟨hN, h1b, h2b, h1P, h2P, h1s, h2s⟩

/-- Second moment: counting the quadruples `p₁ + 2 q₁ = p₂ + 2 q₂ ≤ N` by the difference
`d = |q₂ - q₁|` bounds it by the number of prime pairs at gap `d` times the number at gap `2 d`. -/
private lemma second_moment (N : ℕ) :
    ∑ n ∈ (Icc 1 N).filter Odd, (repCnt n) ^ 2 ≤
      2 * ∑ d ∈ range (N + 1), gapCount d (N + 1) * gapCount (2 * d) (N + 1) := by
  classical
  set T := (Icc 1 N).filter Odd with hT
  set A : ℕ → Finset ℕ := fun d => (range (N + 1)).filter (fun q => q.Prime ∧ (q + d).Prime)
    with hA
  set B : ℕ → Finset ℕ := fun d => (range (N + 1)).filter (fun p => p.Prime ∧ (p + 2 * d).Prime)
    with hB
  have hstep : ∀ n : ℕ, (repCnt n) ^ 2 = #(repSet n ×ˢ repSet n) := by
    intro n
    rw [repCnt, sq, card_product]
  simp_rw [hstep]
  rw [← card_sigma]
  set Total := T.sigma (fun n => repSet n ×ˢ repSet n) with hTotal
  set Target := (range (N + 1)).sigma (fun d => A d ×ˢ B d) with hTarget
  have hsplit : Total.card =
      (Total.filter (fun x => x.2.1 ≤ x.2.2)).card +
      (Total.filter (fun x => ¬ x.2.1 ≤ x.2.2)).card :=
    (card_filter_add_card_filter_not (fun x : Sigma fun n => ℕ × ℕ => x.2.1 ≤ x.2.2)).symm
  have hL : (Total.filter (fun x => x.2.1 ≤ x.2.2)).card ≤ Target.card := by
    refine card_le_card_of_injOn
      (fun x : Sigma fun n => ℕ × ℕ => (⟨x.2.2 - x.2.1, (x.2.1, x.1 - 2 * x.2.2)⟩
        : Sigma fun d => ℕ × ℕ)) ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, hTotal, mem_filter] at hx
      obtain ⟨hxF, hle⟩ := hx
      obtain ⟨hxN, h2q1, h2q2, hq1P, hq2P, hq1sub, hq2sub⟩ := mem_total_facts hxF
      simp only [Finset.mem_coe, hTarget, mem_sigma, mem_product, hA, hB, mem_filter,
        mem_range]
      have hkey : x.1 - 2 * x.2.2 + 2 * (x.2.2 - x.2.1) = x.1 - 2 * x.2.1 := by omega
      refine ⟨by omega, ⟨by omega, hq1P, ?_⟩, ⟨by omega, hq2sub, ?_⟩⟩
      · rw [Nat.add_sub_cancel' hle]; exact hq2P
      · rw [hkey]; exact hq1sub
    · intro a ha b hb hab
      rw [Finset.mem_coe, mem_filter] at ha hb
      obtain ⟨haF, hale⟩ := ha
      obtain ⟨hbF, hble⟩ := hb
      obtain ⟨-, h2qa1, h2qa2, -, -, hqa1sub, hqa2sub⟩ := mem_total_facts haF
      obtain ⟨-, h2qb1, h2qb2, -, -, hqb1sub, hqb2sub⟩ := mem_total_facts hbF
      have hab' : (⟨a.2.2 - a.2.1, (a.2.1, a.1 - 2 * a.2.2)⟩ : Sigma fun d => ℕ × ℕ) =
          ⟨b.2.2 - b.2.1, (b.2.1, b.1 - 2 * b.2.2)⟩ := hab
      injection hab' with h1 h2
      injection h2 with h3 h4
      have h5 : a.2.2 = b.2.2 := by omega
      have h6 : a.1 = b.1 := by omega
      exact Sigma.ext h6 (heq_of_eq (Prod.ext h3 h5))
  have hR : (Total.filter (fun x => ¬ x.2.1 ≤ x.2.2)).card ≤ Target.card := by
    refine card_le_card_of_injOn
      (fun x : Sigma fun n => ℕ × ℕ => (⟨x.2.1 - x.2.2, (x.2.2, x.1 - 2 * x.2.1)⟩
        : Sigma fun d => ℕ × ℕ)) ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, hTotal, mem_filter] at hx
      obtain ⟨hxF, hle⟩ := hx
      obtain ⟨hxN, h2q1, h2q2, hq1P, hq2P, hq1sub, hq2sub⟩ := mem_total_facts hxF
      have hlt : x.2.2 < x.2.1 := by omega
      simp only [Finset.mem_coe, hTarget, mem_sigma, mem_product, hA, hB, mem_filter,
        mem_range]
      have hkey : x.1 - 2 * x.2.1 + 2 * (x.2.1 - x.2.2) = x.1 - 2 * x.2.2 := by omega
      refine ⟨by omega, ⟨by omega, hq2P, ?_⟩, ⟨by omega, hq1sub, ?_⟩⟩
      · rw [Nat.add_sub_cancel' hlt.le]; exact hq1P
      · rw [hkey]; exact hq2sub
    · intro a ha b hb hab
      rw [Finset.mem_coe, mem_filter] at ha hb
      obtain ⟨haF, hale⟩ := ha
      obtain ⟨hbF, hble⟩ := hb
      obtain ⟨-, h2qa1, h2qa2, -, -, hqa1sub, hqa2sub⟩ := mem_total_facts haF
      obtain ⟨-, h2qb1, h2qb2, -, -, hqb1sub, hqb2sub⟩ := mem_total_facts hbF
      have hab' : (⟨a.2.1 - a.2.2, (a.2.2, a.1 - 2 * a.2.1)⟩ : Sigma fun d => ℕ × ℕ) =
          ⟨b.2.1 - b.2.2, (b.2.2, b.1 - 2 * b.2.1)⟩ := hab
      injection hab' with h1 h2
      injection h2 with h3 h4
      have h5 : a.2.1 = b.2.1 := by omega
      have h6 : a.1 = b.1 := by omega
      exact Sigma.ext h6 (heq_of_eq (Prod.ext h5 h3))
  have hTargetCard : Target.card =
      ∑ d ∈ range (N + 1), gapCount d (N + 1) * gapCount (2 * d) (N + 1) := by
    rw [hTarget, card_sigma]
    exact Finset.sum_congr rfl fun d _ => by rw [card_product]; rfl
  have hL' : #(Total.filter (fun x => x.2.1 ≤ x.2.2)) ≤
      ∑ d ∈ range (N + 1), gapCount d (N + 1) * gapCount (2 * d) (N + 1) := by
    rw [← hTargetCard]; exact hL
  have hR' : #(Total.filter (fun x => ¬ x.2.1 ≤ x.2.2)) ≤
      ∑ d ∈ range (N + 1), gapCount d (N + 1) * gapCount (2 * d) (N + 1) := by
    rw [← hTargetCard]; exact hR
  rw [hsplit]
  linarith [hL', hR']

/-! ### The gaps `2 d` and `d` -/

/-- `log t ≤ 4 t^(1/4)`, from `log y ≤ y - 1`. -/
private lemma lemoine_log_four_rpow (t : ℝ) (ht : 0 < t) : Real.log t ≤ 4 * t ^ (1 / 4 : ℝ) := by
  have h1 : Real.log t = 4 * Real.log (t ^ (1 / 4 : ℝ)) := by
    rw [Real.log_rpow ht]
    ring
  have h3 : (0 : ℝ) < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have h2 : Real.log (t ^ (1 / 4 : ℝ)) ≤ t ^ (1 / 4 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos h3
  rw [h1]
  linarith

/-- For `t ≥ 256`, `(log t)² ≤ t`. -/
private lemma log_sq_le_self {t : ℝ} (ht : 256 ≤ t) : Real.log t ^ 2 ≤ t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have h := lemoine_log_four_rpow t ht0
  have hr : (t ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt t := by
    rw [pow_two, ← Real.rpow_add ht0, Real.sqrt_eq_rpow]
    norm_num
  have h4 : (4 * t ^ (1 / 4 : ℝ)) ^ 2 = 16 * Real.sqrt t := by
    rw [mul_pow, hr]; ring
  have h16 : 16 ≤ Real.sqrt t := by
    have h1 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
    nlinarith [Real.sqrt_nonneg t]
  have hpos4 : (0 : ℝ) ≤ 4 * t ^ (1 / 4 : ℝ) :=
    le_of_lt (by have := Real.rpow_pos_of_pos ht0 (1 / 4 : ℝ); linarith)
  have hsq : Real.log t ^ 2 ≤ (4 * t ^ (1 / 4 : ℝ)) ^ 2 := by nlinarith [h, hlog0, hpos4]
  have h16t : 16 * Real.sqrt t ≤ t := by nlinarith [h16, Real.sqrt_nonneg t, Real.sq_sqrt ht0.le]
  linarith [hsq, h4, h16t]

/-- An odd gap leaves at most the pair `(2, 2 + d)`. -/
private lemma gapCount_odd_le_one (d M : ℕ) (ho : Odd d) : gapCount d M ≤ 1 := by
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · simp at ho
    · exact h
  have hsub : (range M).filter (fun p => p.Prime ∧ (p + d).Prime) ⊆ {2} := by
    intro p hp
    simp only [mem_filter, mem_range, mem_singleton] at hp ⊢
    by_contra hne
    have hp2 : 2 ≤ p := hp.2.1.two_le
    have hpodd : Odd p := hp.2.1.odd_of_ne_two (by omega)
    have heven : Even (p + d) := hpodd.add_odd ho
    have h2eq := hp.2.2.even_iff.mp heven
    omega
  unfold gapCount
  exact (card_le_card hsub).trans (by simp)

/-- Uniform Brun bound for every gap `d ≥ 1`: for odd `d` the count is at most one, and
`1 ≤ C singProd d M / log² M` once `M ≥ 256`. -/
private lemma gapCount_le_uniform {d M : ℕ} (hd : 1 ≤ d) (hM : 256 ≤ M) :
    (gapCount d M : ℝ) ≤ (128 + 5 * 17 ^ 8) * singProd d * M / Real.log M ^ 2 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have h1M : (1 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 1 < M)
  have hlog : 0 < Real.log M ^ 2 := by
    have := Real.log_pos h1M
    positivity
  have hbig : (1 : ℝ) ≤ M / Real.log M ^ 2 := by
    rw [le_div_iff₀ hlog]
    have h := log_sq_le_self (t := (M : ℝ)) (by exact_mod_cast hM)
    linarith
  have hC : (1 : ℝ) ≤ 128 + 5 * 17 ^ 8 := by norm_num
  have hsp : (1 : ℝ) ≤ singProd d := one_le_singProd d
  have hC' : (1 : ℝ) ≤ (128 + 5 * 17 ^ 8) * singProd d := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (128 + 5 * 17 ^ 8) * singProd d :=
          mul_le_mul hC hsp (by norm_num) (by linarith)
  have hone : (1 : ℝ) ≤ (128 + 5 * 17 ^ 8) * singProd d * M / Real.log M ^ 2 := by
    have h3 : (1 : ℝ) ≤ ((128 + 5 * 17 ^ 8) * singProd d) * (M / Real.log M ^ 2) := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ ((128 + 5 * 17 ^ 8) * singProd d) * (M / Real.log M ^ 2) :=
            mul_le_mul hC' hbig (by norm_num) (by linarith)
    calc (1 : ℝ) ≤ ((128 + 5 * 17 ^ 8) * singProd d) * (M / Real.log M ^ 2) := h3
      _ = (128 + 5 * 17 ^ 8) * singProd d * M / Real.log M ^ 2 := by ring
  rcases Nat.even_or_odd d with he | ho
  · exact gapUniform d M he (by omega) (by omega)
  · refine le_trans ?_ hone
    have := gapCount_odd_le_one d M ho
    exact_mod_cast this

/-- `singProd (2 d) ≤ 3/2 · singProd d`. -/
private lemma singProd_two_mul_le (d : ℕ) : singProd (2 * d) ≤ 3 / 2 * singProd d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [singProd, Nat.primeFactors_zero, Finset.prod_empty]
    norm_num
  · have hd0 : d ≠ 0 := hd.ne'
    have hpq : (2 * d).primeFactors = insert 2 d.primeFactors := by
      rw [Nat.primeFactors_mul (by norm_num : (2 : ℕ) ≠ 0) hd0, Nat.prime_two.primeFactors,
        Finset.singleton_union]
    have hmono : singProd (2 * d) = ∏ p ∈ insert 2 d.primeFactors, (1 + 1 / (p : ℝ)) := by
      rw [singProd, hpq]
    by_cases h2 : (2 : ℕ) ∈ d.primeFactors
    · rw [hmono, Finset.insert_eq_of_mem h2]
      have hp : (0 : ℝ) ≤ ∏ p ∈ d.primeFactors, (1 + 1 / (p : ℝ)) :=
        Finset.prod_nonneg fun p _ => by positivity
      rw [singProd]
      linarith
    · rw [hmono, Finset.prod_insert h2, singProd]
      rw [show (1 : ℝ) + 1 / ((2 : ℕ) : ℝ) = 3 / 2 by norm_num]

/-- `log t ≤ 8 t^(1/8)`, from `log y ≤ y - 1`. -/
private lemma lemoine_log_eight_rpow (t : ℝ) (ht : 0 < t) : Real.log t ≤ 8 * t ^ (1 / 8 : ℝ) := by
  have h1 : Real.log t = 8 * Real.log (t ^ (1 / 8 : ℝ)) := by
    rw [Real.log_rpow ht]
    ring
  have h3 : (0 : ℝ) < t ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos ht _
  have h2 : Real.log (t ^ (1 / 8 : ℝ)) ≤ t ^ (1 / 8 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos h3
  rw [h1]
  linarith

/-- `(log t)^4 ≤ t` for `t ≥ 17 · 10^6`. -/
private lemma log_pow_four_le_self {t : ℝ} (ht : 17000000 ≤ t) : Real.log t ^ 4 ≤ t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have h := lemoine_log_eight_rpow t ht0
  have hpos : (0 : ℝ) ≤ 8 * t ^ (1 / 8 : ℝ) :=
    le_of_lt (by have := Real.rpow_pos_of_pos ht0 (1 / 8 : ℝ); linarith)
  have hs4 : (t ^ (1 / 8 : ℝ)) ^ 2 = t ^ (1 / 4 : ℝ) := by
    rw [pow_two, ← Real.rpow_add ht0]
    norm_num
  have hr : (t ^ (1 / 8 : ℝ)) ^ 4 = Real.sqrt t := by
    have h1 : (t ^ (1 / 8 : ℝ)) ^ 4 = ((t ^ (1 / 8 : ℝ)) ^ 2) ^ 2 := by ring
    rw [h1, hs4, pow_two, ← Real.rpow_add ht0, Real.sqrt_eq_rpow]
    norm_num
  have hsq2 : Real.log t ^ 2 ≤ (8 * t ^ (1 / 8 : ℝ)) ^ 2 := by nlinarith [h, hlog0, hpos]
  have hsq : Real.log t ^ 4 ≤ (8 * t ^ (1 / 8 : ℝ)) ^ 4 := by
    nlinarith [hsq2, hlog0, hpos]
  have hval : (8 * t ^ (1 / 8 : ℝ)) ^ 4 = 4096 * Real.sqrt t := by
    rw [mul_pow, hr]; norm_num
  have h16 : 4096 ≤ Real.sqrt t := by
    have h1 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
    nlinarith [Real.sqrt_nonneg t]
  have hfin : 4096 * Real.sqrt t ≤ t := by
    nlinarith [h16, Real.sqrt_nonneg t, Real.sq_sqrt ht0.le]
  linarith [hsq, hval, hfin]

/-- The sum of the gap counts over all gaps `d ≤ N` is `O(N³ / log⁴ N)`. -/
private lemma gap_sum_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 10 ^ 10 ≤ N →
      ∑ d ∈ range (N + 1), (gapCount d (N + 1) : ℝ) * (gapCount (2 * d) (N + 1) : ℝ) ≤
        K * (N : ℝ) ^ 3 / Real.log N ^ 4 := by
  obtain ⟨D, hD⟩ := S2_holds_route
  have hDpos : 0 < D := by
    have h1 := hD 1 le_rfl
    have h2 : (1 : ℝ) ≤ ∑ n ∈ Icc 1 1, singProd n ^ 2 := by
      have : (Icc 1 1 : Finset ℕ) = {1} := by decide
      rw [this, Finset.sum_singleton]
      have : singProd 1 = 1 := by simp [singProd]
      rw [this]; norm_num
    have : (1:ℝ) ≤ D * 1 := le_trans h2 (by simpa using h1)
    linarith
  set C : ℝ := 128 + 5 * 17 ^ 8 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; norm_num
  refine ⟨12 * C ^ 2 * D + 8, by positivity, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlog4 : 0 < Real.log N ^ 4 := by positivity
  have hM256 : 256 ≤ N + 1 := by omega
  have hMbig : 17000000 ≤ (N : ℝ) := by exact_mod_cast (by norm_num; omega)
  have hMle : ((N : ℝ) + 1) ≤ 2 * N := by linarith
  have hlogM : Real.log N ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlogM4 : 0 < Real.log ((N : ℝ) + 1) ^ 4 := by
    have : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
    positivity
  -- split off `d = 0`
  have hrange : (range (N + 1)) = insert 0 (Icc 1 N) := by
    ext d
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hrange, Finset.sum_insert (by simp)]
  -- the `d = 0` term
  have hM0 : gapCount 0 (N + 1) ≤ N + 1 := by
    unfold gapCount
    calc #((range (N + 1)).filter (fun p => p.Prime ∧ (p + 0).Prime)) ≤ #(range (N + 1)) :=
          card_le_card (filter_subset _ _)
      _ = N + 1 := card_range _
  have hM0' : gapCount (2 * 0) (N + 1) ≤ N + 1 := by
    unfold gapCount
    calc #((range (N + 1)).filter (fun p => p.Prime ∧ (p + 2 * 0).Prime)) ≤ #(range (N + 1)) :=
          card_le_card (filter_subset _ _)
      _ = N + 1 := card_range _
  have hzero : (gapCount 0 (N + 1) : ℝ) * (gapCount (2 * 0) (N + 1) : ℝ) ≤
      ((N : ℝ) + 1) ^ 2 := by
    have h1 : (gapCount 0 (N + 1) : ℝ) ≤ (N : ℝ) + 1 := by
      have h := hM0
      push_cast
      exact_mod_cast h
    have h2 : (gapCount (2 * 0) (N + 1) : ℝ) ≤ (N : ℝ) + 1 := by
      have h := hM0'
      push_cast
      exact_mod_cast h
    calc (gapCount 0 (N + 1) : ℝ) * (gapCount (2 * 0) (N + 1) : ℝ)
        ≤ ((N : ℝ) + 1) * ((N : ℝ) + 1) :=
          mul_le_mul h1 h2 (Nat.cast_nonneg _) (by linarith)
      _ = ((N : ℝ) + 1) ^ 2 := by ring
  -- the uniform bound on each gap pair
  have hterm : ∀ d ∈ Icc 1 N,
      (gapCount d (N + 1) : ℝ) * (gapCount (2 * d) (N + 1) : ℝ) ≤
        C ^ 2 * (singProd d * singProd (2 * d)) * ((N : ℝ) + 1) ^ 2 /
          Real.log ((N : ℝ) + 1) ^ 4 := by
    intro d hd
    obtain ⟨hd1, -⟩ := mem_Icc.1 hd
    have h1 : (gapCount d (N + 1) : ℝ) ≤ C * singProd d * ((N : ℝ) + 1) /
        Real.log ((N : ℝ) + 1) ^ 2 := by
      have h := gapCount_le_uniform (d := d) hd1 hM256
      rw [← hCdef] at h
      push_cast at h
      exact h
    have h2 : (gapCount (2 * d) (N + 1) : ℝ) ≤ C * singProd (2 * d) * ((N : ℝ) + 1) /
        Real.log ((N : ℝ) + 1) ^ 2 := by
      have h := gapCount_le_uniform (d := 2 * d) (by omega) hM256
      rw [← hCdef] at h
      push_cast at h
      exact h
    have hpos1 : (0 : ℝ) < Real.log ((N : ℝ) + 1) ^ 2 := by
      have h0 : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
      exact pow_pos h0 2
    have hR : (0 : ℝ) ≤ C * singProd d * ((N : ℝ) + 1) / Real.log ((N : ℝ) + 1) ^ 2 := by
      apply div_nonneg _ hpos1.le
      have hsp := singProd_nonneg d
      have hN1' : (0 : ℝ) ≤ (N : ℝ) + 1 := by linarith
      exact mul_nonneg (mul_nonneg hCpos.le hsp) hN1'
    calc (gapCount d (N + 1) : ℝ) * (gapCount (2 * d) (N + 1) : ℝ)
        ≤ (C * singProd d * ((N : ℝ) + 1) / Real.log ((N : ℝ) + 1) ^ 2) *
            (C * singProd (2 * d) * ((N : ℝ) + 1) / Real.log ((N : ℝ) + 1) ^ 2) :=
          mul_le_mul h1 h2 (Nat.cast_nonneg _) hR
      _ = C ^ 2 * (singProd d * singProd (2 * d)) * ((N : ℝ) + 1) ^ 2 /
            Real.log ((N : ℝ) + 1) ^ 4 := by
          have h0 : Real.log ((N : ℝ) + 1) ≠ 0 := by
            have : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
            exact this.ne'
          field_simp
  -- sum the terms
  have hsumraw : ∑ d ∈ Icc 1 N, (gapCount d (N + 1) : ℝ) * (gapCount (2 * d) (N + 1) : ℝ) ≤
      C ^ 2 * ((N : ℝ) + 1) ^ 2 / Real.log ((N : ℝ) + 1) ^ 4 * (3 / 2 * (D * N)) := by
    have hstep1 : ∑ d ∈ Icc 1 N, (gapCount d (N + 1) : ℝ) * (gapCount (2 * d) (N + 1) : ℝ) ≤
        ∑ d ∈ Icc 1 N, C ^ 2 * (singProd d * singProd (2 * d)) * ((N : ℝ) + 1) ^ 2 /
          Real.log ((N : ℝ) + 1) ^ 4 := Finset.sum_le_sum hterm
    have hstep2 : ∑ d ∈ Icc 1 N, C ^ 2 * (singProd d * singProd (2 * d)) * ((N : ℝ) + 1) ^ 2 /
          Real.log ((N : ℝ) + 1) ^ 4 =
        C ^ 2 * ((N : ℝ) + 1) ^ 2 / Real.log ((N : ℝ) + 1) ^ 4 *
          ∑ d ∈ Icc 1 N, singProd d * singProd (2 * d) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
    have hstep3 : ∑ d ∈ Icc 1 N, singProd d * singProd (2 * d) ≤ 3 / 2 * (D * N) := by
      have ha : ∑ d ∈ Icc 1 N, singProd d * singProd (2 * d) ≤
          ∑ d ∈ Icc 1 N, 3 / 2 * singProd d ^ 2 := by
        apply Finset.sum_le_sum
        intro d _
        calc singProd d * singProd (2 * d) ≤ singProd d * (3 / 2 * singProd d) :=
              mul_le_mul_of_nonneg_left (singProd_two_mul_le d) (singProd_nonneg d)
          _ = 3 / 2 * singProd d ^ 2 := by ring
      have hb : ∑ d ∈ Icc 1 N, 3 / 2 * singProd d ^ 2 =
          3 / 2 * ∑ d ∈ Icc 1 N, singProd d ^ 2 := by rw [Finset.mul_sum]
      have hc := hD N (by omega)
      linarith [ha, hb, hc]
    have hposfac : (0 : ℝ) ≤ C ^ 2 * ((N : ℝ) + 1) ^ 2 / Real.log ((N : ℝ) + 1) ^ 4 := by
      apply div_nonneg
      · have hN1' : (0 : ℝ) ≤ (N : ℝ) + 1 := by linarith
        exact mul_nonneg (by positivity) (by positivity)
      · exact hlogM4.le
    calc ∑ d ∈ Icc 1 N, (gapCount d (N + 1) : ℝ) * (gapCount (2 * d) (N + 1) : ℝ)
        ≤ ∑ d ∈ Icc 1 N, C ^ 2 * (singProd d * singProd (2 * d)) * ((N : ℝ) + 1) ^ 2 /
            Real.log ((N : ℝ) + 1) ^ 4 := hstep1
      _ = C ^ 2 * ((N : ℝ) + 1) ^ 2 / Real.log ((N : ℝ) + 1) ^ 4 *
            ∑ d ∈ Icc 1 N, singProd d * singProd (2 * d) := hstep2
      _ ≤ C ^ 2 * ((N : ℝ) + 1) ^ 2 / Real.log ((N : ℝ) + 1) ^ 4 * (3 / 2 * (D * N)) :=
          mul_le_mul_of_nonneg_left hstep3 hposfac
  -- replace `(N+1)` by `2 N` and `log (N+1)` by `log N`
  have hlog4N : Real.log N ^ 4 ≤ N := log_pow_four_le_self hMbig
  have hN1' : (1 : ℝ) ≤ N := hN1
  have hM2 : ((N : ℝ) + 1) ^ 2 ≤ 4 * N ^ 2 := by nlinarith
  have hlog4M : Real.log N ^ 4 ≤ Real.log ((N : ℝ) + 1) ^ 4 := by
    have h2 : Real.log N ^ 2 ≤ Real.log ((N : ℝ) + 1) ^ 2 := by
      have := hlogN
      nlinarith [hlogM]
    have h3 : (0:ℝ) ≤ Real.log N ^ 2 := by positivity
    have h4 : (0:ℝ) ≤ Real.log ((N : ℝ) + 1) ^ 2 := by positivity
    nlinarith [h2, h3, h4]
  have hfac : (0 : ℝ) ≤ 3 / 2 * (D * N) := by nlinarith [hDpos, hNpos]
  have hstep1 : C ^ 2 * ((N : ℝ) + 1) ^ 2 / Real.log ((N : ℝ) + 1) ^ 4 ≤
      C ^ 2 * (4 * N ^ 2) / Real.log N ^ 4 := by
    rw [div_le_div_iff₀ hlogM4 hlog4]
    nlinarith [hM2, hlog4M, hCpos, hlogM4, hlog4]
  have hsum : ∑ d ∈ Icc 1 N, (gapCount d (N + 1) : ℝ) * (gapCount (2 * d) (N + 1) : ℝ) ≤
      6 * C ^ 2 * D * (N : ℝ) ^ 3 / Real.log N ^ 4 := by
    have hC2 : (0 : ℝ) ≤ C ^ 2 := by positivity
    calc ∑ d ∈ Icc 1 N, (gapCount d (N + 1) : ℝ) * (gapCount (2 * d) (N + 1) : ℝ)
        ≤ C ^ 2 * ((N : ℝ) + 1) ^ 2 / Real.log ((N : ℝ) + 1) ^ 4 * (3 / 2 * (D * N)) := hsumraw
      _ ≤ (C ^ 2 * (4 * N ^ 2) / Real.log N ^ 4) * (3 / 2 * (D * N)) :=
          mul_le_mul_of_nonneg_right hstep1 hfac
      _ = 6 * C ^ 2 * D * (N : ℝ) ^ 3 / Real.log N ^ 4 := by
          have h0 : Real.log N ≠ 0 := hlogN.ne'
          field_simp
          ring
  have hzero' : ((N : ℝ) + 1) ^ 2 ≤ 4 * (N : ℝ) ^ 3 / Real.log N ^ 4 := by
    rw [le_div_iff₀ hlog4]
    nlinarith [hM2, hlog4N, hNpos]
  have hZ : (gapCount 0 (N + 1) : ℝ) * (gapCount (2 * 0) (N + 1) : ℝ) ≤
      4 * (N : ℝ) ^ 3 / Real.log N ^ 4 := le_trans hzero hzero'
  have e : (12 * C ^ 2 * D + 8) * (N : ℝ) ^ 3 / Real.log N ^ 4 =
      12 * (C ^ 2 * D * (N : ℝ) ^ 3 / Real.log N ^ 4) + 8 * ((N : ℝ) ^ 3 / Real.log N ^ 4) := by
    ring
  have hm : (0 : ℝ) ≤ C ^ 2 * D * (N : ℝ) ^ 3 / Real.log N ^ 4 := by
    apply div_nonneg _ hlog4.le
    exact mul_nonneg (mul_nonneg (by positivity) hDpos.le) (by positivity)
  have hm2 : (0 : ℝ) ≤ (N : ℝ) ^ 3 / Real.log N ^ 4 :=
    div_nonneg (by positivity) hlog4.le
  have hsum12 : ∑ d ∈ Icc 1 N, (gapCount d (N + 1) : ℝ) * (gapCount (2 * d) (N + 1) : ℝ) ≤
      12 * (C ^ 2 * D * (N : ℝ) ^ 3 / Real.log N ^ 4) := by
    have h6 : 6 * (C ^ 2 * D * (N : ℝ) ^ 3 / Real.log N ^ 4) =
        6 * C ^ 2 * D * (N : ℝ) ^ 3 / Real.log N ^ 4 := by ring
    calc ∑ d ∈ Icc 1 N, (gapCount d (N + 1) : ℝ) * (gapCount (2 * d) (N + 1) : ℝ)
        ≤ 6 * C ^ 2 * D * (N : ℝ) ^ 3 / Real.log N ^ 4 := hsum
      _ = 6 * (C ^ 2 * D * (N : ℝ) ^ 3 / Real.log N ^ 4) := h6.symm
      _ ≤ 12 * (C ^ 2 * D * (N : ℝ) ^ 3 / Real.log N ^ 4) := by linarith [hm]
  have hZ8 : (gapCount 0 (N + 1) : ℝ) * (gapCount (2 * 0) (N + 1) : ℝ) ≤
      8 * ((N : ℝ) ^ 3 / Real.log N ^ 4) := by
    have h4 : 4 * ((N : ℝ) ^ 3 / Real.log N ^ 4) = 4 * (N : ℝ) ^ 3 / Real.log N ^ 4 := by ring
    calc (gapCount 0 (N + 1) : ℝ) * (gapCount (2 * 0) (N + 1) : ℝ)
        ≤ 4 * (N : ℝ) ^ 3 / Real.log N ^ 4 := hZ
      _ = 4 * ((N : ℝ) ^ 3 / Real.log N ^ 4) := h4.symm
      _ ≤ 8 * ((N : ℝ) ^ 3 / Real.log N ^ 4) := by linarith [hm2]
  rw [e]
  linarith [hsum12, hZ8]

/-! ### Cauchy-Schwarz and the density -/

/-- `π m ≥ 2` for `m ≥ 3`. -/
private lemma primeCounting_two_le {m : ℕ} (hm : 3 ≤ m) : 2 ≤ Nat.primeCounting m := by
  have hsub : ({2, 3} : Finset ℕ) ⊆ Nat.primesBelow (m + 1) := by
    intro p hp
    simp only [Nat.mem_primesBelow, mem_insert, mem_singleton] at hp ⊢
    rcases hp with rfl | rfl
    · exact ⟨by omega, Nat.prime_two⟩
    · exact ⟨by omega, Nat.prime_three⟩
  have h1 : Nat.primeCounting m = #(Nat.primesBelow (m + 1)) := primeCounting_eq_card m
  rw [h1]
  have h2 := card_le_card hsub
  simpa using h2

/-- The numbers with a representation are Lemoine numbers. -/
private lemma card_reps_le (N : ℕ) :
    (#((Icc 1 N).filter (fun n => Odd n ∧ 0 < repCnt n)) : ℝ) ≤
      (({n : ℕ | Odd n ∧ IsLemoine n} ∩ Set.Iic N).ncard : ℝ) := by
  have hsub : (((Icc 1 N).filter (fun n => Odd n ∧ 0 < repCnt n) : Finset ℕ) : Set ℕ) ⊆
      {n : ℕ | Odd n ∧ IsLemoine n} ∩ Set.Iic N := by
    intro n hn
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_Iic] at hn ⊢
    obtain ⟨⟨-, hNle⟩, hodd, hpos⟩ := hn
    exact ⟨⟨hodd, isLemoine_of_repCnt_pos hpos⟩, hNle⟩
  calc (#((Icc 1 N).filter (fun n => Odd n ∧ 0 < repCnt n)) : ℝ)
      = ((((Icc 1 N).filter (fun n => Odd n ∧ 0 < repCnt n) : Finset ℕ) : Set ℕ).ncard : ℝ) := by
        rw [Set.ncard_coe_finset]
    _ ≤ (({n : ℕ | Odd n ∧ IsLemoine n} ∩ Set.Iic N).ncard : ℝ) := by
        have := Set.ncard_le_ncard hsub
        exact_mod_cast this

/-- Cauchy-Schwarz on the support of `repCnt`. -/
private lemma cauchy_schwarz_rep (N : ℕ) :
    (∑ n ∈ (Icc 1 N).filter Odd, (repCnt n : ℝ)) ^ 2 ≤
      (#((Icc 1 N).filter (fun n => Odd n ∧ 0 < repCnt n)) : ℝ) *
        ∑ n ∈ (Icc 1 N).filter Odd, ((repCnt n : ℝ)) ^ 2 := by
  set T := (Icc 1 N).filter Odd with hT
  set s := T.filter (fun n => 0 < repCnt n) with hs
  have hsum : ∑ n ∈ T, (repCnt n : ℝ) = ∑ n ∈ s, (repCnt n : ℝ) := by
    have key : ∑ n ∈ T.filter (fun n => 0 < repCnt n), (repCnt n : ℝ) =
        ∑ n ∈ T, (repCnt n : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      split_ifs with h
      · rfl
      · simp [Nat.eq_zero_of_not_pos h]
    rw [hs]
    exact key.symm
  have hs2 : ∑ n ∈ s, ((repCnt n : ℝ)) ^ 2 ≤ ∑ n ∈ T, ((repCnt n : ℝ)) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (by rw [hs]; exact filter_subset _ _)
      (fun _ _ _ => by positivity)
  have hcard : s.card = #((Icc 1 N).filter (fun n => Odd n ∧ 0 < repCnt n)) := by
    rw [hs, hT, Finset.filter_filter]
  calc (∑ n ∈ T, (repCnt n : ℝ)) ^ 2
      = (∑ n ∈ s, (repCnt n : ℝ)) ^ 2 := by rw [hsum]
    _ ≤ (s.card : ℝ) * ∑ n ∈ s, ((repCnt n : ℝ)) ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ (s.card : ℝ) * ∑ n ∈ T, ((repCnt n : ℝ)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left hs2
        positivity
    _ = (#((Icc 1 N).filter (fun n => Odd n ∧ 0 < repCnt n)) : ℝ) *
          ∑ n ∈ T, ((repCnt n : ℝ)) ^ 2 := by rw [hcard]

/-- **Positive lower density of the Lemoine numbers.** Cauchy-Schwarz: the first moment is at
least `(π(N/2) - 1) π(N/4) ≫ N²/log²N`, the second is `O(N³/log⁴ N)`. -/
theorem lemoine_positive_density_aux :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      c * N ≤ (({n : ℕ | Odd n ∧ IsLemoine n} ∩ Set.Iic N).ncard : ℝ) := by
  obtain ⟨K, hKpos, hK⟩ := gap_sum_bound
  obtain ⟨cpi, hcpi, m0, hpi⟩ := pi_lower
  have hcpi4 : 0 < cpi ^ 4 / (8192 * K) := by positivity
  refine ⟨cpi ^ 4 / (8192 * K), hcpi4, max (10 ^ 20) (4 * m0 + 8), fun N hN => ?_⟩
  have hbig20 : 10 ^ 20 ≤ N := le_trans (le_max_left _ _) hN
  have hm0le : 4 * m0 + 8 ≤ N := le_trans (le_max_right _ _) hN
  have hNbig : 10 ^ 10 ≤ N := by norm_num at hbig20 ⊢; omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlog2 : 0 < Real.log N ^ 2 := by positivity
  have hlog4 : 0 < Real.log N ^ 4 := by positivity
  have hNR : (10 ^ 20 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hbig20
  set T := (Icc 1 N).filter Odd with hT
  -- `log N ≤ sqrt N`, so the size factors are harmless
  have hlogsqrt : Real.log N ≤ Real.sqrt N := by
    have hbig256 : (256 : ℝ) ≤ N := by
      have : (256 : ℕ) ≤ N := by norm_num; omega
      exact_mod_cast this
    have h := log_sq_le_self (t := (N : ℝ)) hbig256
    have h0 : 0 ≤ Real.log N := hlogN.le
    have hs : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt hNpos.le
    nlinarith [h, h0, Real.sqrt_nonneg N]
  have hsqrtbig : (10000000000 : ℝ) ≤ Real.sqrt N := by
    have hs : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt hNpos.le
    nlinarith [Real.sqrt_nonneg N]
  -- first moment, lower bound
  have hm1 : (Nat.primeCounting (N / 2) - 1) * Nat.primeCounting (N / 4) ≤
      ∑ n ∈ T, repCnt n := by
    rw [hT]; exact first_moment N (by omega)
  have hm1R : (((Nat.primeCounting (N / 2) - 1) * Nat.primeCounting (N / 4) : ℕ) : ℝ) ≤
      ∑ n ∈ T, (repCnt n : ℝ) := by
    have h := hm1
    push_cast
    exact_mod_cast h
  have hpi1 : cpi * (N : ℝ) / (8 * Real.log N) ≤ ((Nat.primeCounting (N / 2) : ℕ) : ℝ) - 1 := by
    have hm : m0 ≤ N / 2 := by omega
    have h1 := hpi (N / 2) hm
    have hposhalf : 0 < Real.log ((N / 2 : ℕ) : ℝ) := by
      apply Real.log_pos
      have h2 : (2 : ℕ) ≤ N / 2 := by omega
      have : (2 : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    have hle : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) := by
      have h2 : N / 2 ≤ N := Nat.div_le_self N 2
      exact_mod_cast h2
    have hloghalf : Real.log ((N / 2 : ℕ) : ℝ) ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < N / 2)) hle
    have hN2ge : (N : ℝ) / 4 ≤ ((N / 2 : ℕ) : ℝ) := by
      have h : N ≤ 4 * (N / 2) := by omega
      have h' : (N : ℝ) ≤ 4 * ((N / 2 : ℕ) : ℝ) := by exact_mod_cast h
      linarith
    have hcN : (0 : ℝ) < cpi * (N : ℝ) := by nlinarith [hcpi, hNpos]
    have hge : cpi * (N : ℝ) / (4 * Real.log N) ≤
        cpi * ((N / 2 : ℕ) : ℝ) / Real.log ((N / 2 : ℕ) : ℝ) := by
      rw [div_le_div_iff₀ (by nlinarith [hlogN]) hposhalf]
      have hL : cpi * (N : ℝ) * Real.log ((N / 2 : ℕ) : ℝ) ≤ cpi * (N : ℝ) * Real.log N :=
        mul_le_mul_of_nonneg_left hloghalf hcN.le
      have hR : cpi * (N : ℝ) * Real.log N ≤ cpi * ((N / 2 : ℕ) : ℝ) * (4 * Real.log N) := by
        have h1 : ((N : ℝ) / 4) * (4 * (cpi * Real.log N)) ≤
            ((N / 2 : ℕ) : ℝ) * (4 * (cpi * Real.log N)) := by
          apply mul_le_mul_of_nonneg_right hN2ge
          nlinarith [hcpi, hlogN]
        linarith [h1]
      linarith [hL, hR]
    have hle2 : cpi * (N : ℝ) / (4 * Real.log N) ≤ ((Nat.primeCounting (N / 2) : ℕ) : ℝ) :=
      le_trans hge h1
    have hpi2ge : (2 : ℝ) ≤ ((Nat.primeCounting (N / 2) : ℕ) : ℝ) := by
      have h2 : 2 ≤ Nat.primeCounting (N / 2) := primeCounting_two_le (by omega)
      exact_mod_cast h2
    have hhalf : cpi * (N : ℝ) / (8 * Real.log N) = (cpi * (N : ℝ) / (4 * Real.log N)) / 2 := by
      field_simp
      ring
    linarith [hle2, hpi2ge, hhalf]
  have hpi2 : cpi * (N : ℝ) / (8 * Real.log N) ≤ ((Nat.primeCounting (N / 4) : ℕ) : ℝ) := by
    have hm : m0 ≤ N / 4 := by omega
    have h1 := hpi (N / 4) hm
    have hpos4 : 0 < Real.log ((N / 4 : ℕ) : ℝ) := by
      apply Real.log_pos
      have h2 : (2 : ℕ) ≤ N / 4 := by omega
      have : (2 : ℝ) ≤ ((N / 4 : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    have hle : ((N / 4 : ℕ) : ℝ) ≤ (N : ℝ) := by
      have h2 : N / 4 ≤ N := Nat.div_le_self N 4
      exact_mod_cast h2
    have hlog4' : Real.log ((N / 4 : ℕ) : ℝ) ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < N / 4)) hle
    have hN4ge : (N : ℝ) / 8 ≤ ((N / 4 : ℕ) : ℝ) := by
      have h : N ≤ 8 * (N / 4) := by omega
      have h' : (N : ℝ) ≤ 8 * ((N / 4 : ℕ) : ℝ) := by exact_mod_cast h
      linarith
    have hcN : (0 : ℝ) < cpi * (N : ℝ) := by nlinarith [hcpi, hNpos]
    have hge : cpi * (N : ℝ) / (8 * Real.log N) ≤
        cpi * ((N / 4 : ℕ) : ℝ) / Real.log ((N / 4 : ℕ) : ℝ) := by
      rw [div_le_div_iff₀ (by nlinarith [hlogN]) hpos4]
      have hL : cpi * (N : ℝ) * Real.log ((N / 4 : ℕ) : ℝ) ≤ cpi * (N : ℝ) * Real.log N :=
        mul_le_mul_of_nonneg_left hlog4' hcN.le
      have hR : cpi * (N : ℝ) * Real.log N ≤ cpi * ((N / 4 : ℕ) : ℝ) * (8 * Real.log N) := by
        have h1 : ((N : ℝ) / 8) * (8 * (cpi * Real.log N)) ≤
            ((N / 4 : ℕ) : ℝ) * (8 * (cpi * Real.log N)) := by
          apply mul_le_mul_of_nonneg_right hN4ge
          nlinarith [hcpi, hlogN]
        linarith [h1]
      linarith [hL, hR]
    linarith
  have hsum_ge : cpi ^ 2 * (N : ℝ) ^ 2 / (64 * Real.log N ^ 2) ≤
      ∑ n ∈ T, (repCnt n : ℝ) := by
    have hcast : ((Nat.primeCounting (N / 2) - 1 : ℕ) : ℝ) =
        ((Nat.primeCounting (N / 2) : ℕ) : ℝ) - 1 := by
      have h1 : 1 ≤ Nat.primeCounting (N / 2) := by
        have h2 : 2 ≤ Nat.primeCounting (N / 2) := primeCounting_two_le (by omega)
        omega
      push_cast [h1]
      ring
    have hA1 : cpi * (N : ℝ) / (8 * Real.log N) ≤ ((Nat.primeCounting (N / 2) - 1 : ℕ) : ℝ) := by
      rw [hcast]; exact hpi1
    have hA2 : cpi * (N : ℝ) / (8 * Real.log N) ≤ ((Nat.primeCounting (N / 4) : ℕ) : ℝ) := hpi2
    have hmul := mul_le_mul hA1 hA2 (by positivity) (by positivity)
    have heq : (cpi * (N : ℝ) / (8 * Real.log N)) * (cpi * (N : ℝ) / (8 * Real.log N)) =
        cpi ^ 2 * (N : ℝ) ^ 2 / (64 * Real.log N ^ 2) := by
      field_simp
      ring
    have hprod : cpi ^ 2 * (N : ℝ) ^ 2 / (64 * Real.log N ^ 2) ≤
        ((Nat.primeCounting (N / 2) - 1 : ℕ) : ℝ) * ((Nat.primeCounting (N / 4) : ℕ) : ℝ) := by
      rw [← heq]
      exact hmul
    have hm1R' : ((Nat.primeCounting (N / 2) - 1 : ℕ) : ℝ) * ((Nat.primeCounting (N / 4) : ℕ) : ℝ) ≤
        ∑ n ∈ T, (repCnt n : ℝ) := by
      have h := hm1R
      push_cast at h ⊢
      exact h
    linarith
  -- second moment, upper bound
  have hm2 : ∑ n ∈ T, ((repCnt n : ℝ)) ^ 2 ≤ 2 * (K * (N : ℝ) ^ 3 / Real.log N ^ 4) := by
    have h2 := second_moment N
    have hcast : ((∑ n ∈ T, (repCnt n) ^ 2 : ℕ) : ℝ) = ∑ n ∈ T, ((repCnt n : ℝ)) ^ 2 := by
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro n _
      push_cast
      ring
    have hK' := hK N hNbig
    have h2c : ((∑ n ∈ T, (repCnt n) ^ 2 : ℕ) : ℝ) ≤ 2 * (K * (N : ℝ) ^ 3 / Real.log N ^ 4) := by
      have hcast2 : ((2 * ∑ d ∈ range (N + 1), gapCount d (N + 1) * gapCount (2 * d) (N + 1) : ℕ) : ℝ)
          = 2 * ∑ d ∈ range (N + 1), (gapCount d (N + 1) : ℝ) * (gapCount (2 * d) (N + 1) : ℝ) := by
        push_cast
        ring
      have h2' : ((∑ n ∈ T, (repCnt n) ^ 2 : ℕ) : ℝ) ≤
          ((2 * ∑ d ∈ range (N + 1), gapCount d (N + 1) * gapCount (2 * d) (N + 1) : ℕ) : ℝ) := by
        have hh : ∑ n ∈ T, (repCnt n) ^ 2 ≤
            2 * ∑ d ∈ range (N + 1), gapCount d (N + 1) * gapCount (2 * d) (N + 1) := by
          rw [hT]; exact h2
        exact_mod_cast hh
      rw [hcast2] at h2'
      linarith [h2', hK']
    rw [← hcast]
    exact h2c
  -- Cauchy-Schwarz and the final arithmetic
  have hCS := cauchy_schwarz_rep N
  rw [← hT] at hCS
  have hA := card_reps_le N
  have hsq_ge : (cpi ^ 2 * (N : ℝ) ^ 2 / (64 * Real.log N ^ 2)) ^ 2 ≤
      (∑ n ∈ T, (repCnt n : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsum_ge 2
  have hfinal : (cpi ^ 2 * (N : ℝ) ^ 2 / (64 * Real.log N ^ 2)) ^ 2 ≤
      (({n : ℕ | Odd n ∧ IsLemoine n} ∩ Set.Iic N).ncard : ℝ) *
        (2 * (K * (N : ℝ) ^ 3 / Real.log N ^ 4)) := by
    calc (cpi ^ 2 * (N : ℝ) ^ 2 / (64 * Real.log N ^ 2)) ^ 2
        ≤ (∑ n ∈ T, (repCnt n : ℝ)) ^ 2 := hsq_ge
      _ ≤ ((Icc 1 N).filter (fun n => Odd n ∧ 0 < repCnt n)).card *
            ∑ n ∈ T, ((repCnt n : ℝ)) ^ 2 := hCS
      _ ≤ (({n : ℕ | Odd n ∧ IsLemoine n} ∩ Set.Iic N).ncard : ℝ) *
            (2 * (K * (N : ℝ) ^ 3 / Real.log N ^ 4)) := by
          apply mul_le_mul hA hm2 (by positivity) (by positivity)
  have e1 : (cpi ^ 2 * (N : ℝ) ^ 2 / (64 * Real.log N ^ 2)) ^ 2 =
      cpi ^ 4 * (N : ℝ) ^ 4 / (4096 * Real.log N ^ 4) := by
    field_simp
    ring
  rw [e1] at hfinal
  have hpos : 0 < 2 * (K * (N : ℝ) ^ 3 / Real.log N ^ 4) := by positivity
  have hdiv : cpi ^ 4 * (N : ℝ) ^ 4 / (4096 * Real.log N ^ 4) /
      (2 * (K * (N : ℝ) ^ 3 / Real.log N ^ 4)) ≤
      (({n : ℕ | Odd n ∧ IsLemoine n} ∩ Set.Iic N).ncard : ℝ) := by
    rw [div_le_iff₀ hpos]
    linarith [hfinal]
  have heq : cpi ^ 4 * (N : ℝ) ^ 4 / (4096 * Real.log N ^ 4) /
      (2 * (K * (N : ℝ) ^ 3 / Real.log N ^ 4)) = cpi ^ 4 / (8192 * K) * (N : ℝ) := by
    have hKne : K ≠ 0 := hKpos.ne'
    have hlogne : Real.log N ≠ 0 := hlogN.ne'
    field_simp
    ring
  linarith [hdiv, heq]

end

/-- Unit U-1603, route lemma, PROVED. Plain math: the odd numbers of the form `p + 2 q` have positive
lower density, the Lemoine twin of the lab's `S3_positive_lower_density` in `SchnirelmannGoldbach`.
This is a lab route lemma, NOT a transcription: the Lemoine sources in `Lemoine.lean` state the
conjecture and a count, and no source passage for a density was found. DECISION U-1618 keeps it as
proved text, no re-cut. Nearest prior art read: Romanov's theorem, a prime plus a power of 2, and
Elsholtz, Luca, Planitzer, Romanov type problems, Ramanujan J. 47 (2018) 267 to 289, Theorem 2, the
lower density of `p + 2^(2^k) + 2^q` is positive. That is another form, and the filed line's
Weingartner and `2 q` do not match the paper. A short search found no density statement for
`p + 2 q` itself, which is no proof that none exists, and the result is not called new. `Odd n` is
load-bearing, since `IsLemoine 8` holds, and `Set.Iic N` keeps `ncard` honest. Far weaker than
Lemoine's conjecture. -/
theorem route_lemoine_positive_density :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      c * N ≤ (({n : ℕ | Odd n ∧ IsLemoine n} ∩ Set.Iic N).ncard : ℝ) :=
  lemoine_positive_density_aux

section

open LeanLab.BrunGap LeanLab.SchnirelmannGoldbach

/-! Private support for `route_cluster_count_le`, from the lab's Brun bound `gapUpper` for prime
pairs at an even gap `h` (`LeanLab/BrunGap/Final.lean`), imported by the one line added at the top
of this file. Same proof as `results/RouteLemmas_leaf3_modulo_brun.lean`. -/

private lemma singProd_pos' (n : ℕ) : 0 < singProd n := by
  unfold singProd
  refine Finset.prod_pos (fun p hp => ?_)
  have h : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  linarith

/-- primes `9 < p ≤ x` with `p - d` prime. -/
private def S (x d : ℕ) : Set ℕ := {p : ℕ | p.Prime ∧ (p - d).Prime ∧ 9 < p} ∩ Set.Iic x

/-- primes `q < x` with `q + d` prime, the set counted by `gapCount`. -/
private def G (x d : ℕ) : Set ℕ := {q : ℕ | q.Prime ∧ (q + d).Prime} ∩ Set.Iio x

private lemma G_eq (x d : ℕ) :
    G x d = ↑((Finset.range x).filter (fun q => q.Prime ∧ (q + d).Prime)) := by
  ext q
  constructor
  · intro h
    simp only [G, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iio, Finset.coe_filter,
      Finset.mem_range, Set.mem_ofPred_eq] at h ⊢
    exact ⟨h.2, h.1⟩
  · intro h
    simp only [G, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iio, Finset.coe_filter,
      Finset.mem_range, Set.mem_ofPred_eq] at h ⊢
    exact ⟨h.2, h.1⟩

private lemma S_ncard_le (x d : ℕ) (hd0 : 0 < d) (hd : d ≤ 9) : (S x d).ncard ≤ gapCount d x := by
  classical
  have hfin : (G x d).Finite := Set.Finite.subset (Set.finite_Iio x) Set.inter_subset_right
  have hle : (S x d).ncard ≤ (G x d).ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun p => p - d) ?_ ?_ hfin
    · intro p hp
      simp only [S, G, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iio] at hp ⊢
      obtain ⟨⟨hpp, hpd, h9⟩, hpx⟩ := hp
      have hdp : d ≤ p := by omega
      have hlt : p - d < p := Nat.sub_lt (by omega) hd0
      exact ⟨⟨hpd, by rwa [Nat.sub_add_cancel hdp]⟩, Nat.lt_of_lt_of_le hlt hpx⟩
    · intro a ha b hb hab
      simp only [S, G, Set.mem_inter_iff, Set.mem_setOf_eq] at ha hb
      have hda : d ≤ a := by have := ha.1.2.2; omega
      have hdb : d ≤ b := by have := hb.1.2.2; omega
      have hab' : a - d = b - d := hab
      calc a = (a - d) + d := (Nat.sub_add_cancel hda).symm
        _ = (b - d) + d := by rw [hab']
        _ = b := Nat.sub_add_cancel hdb
  rw [G_eq, Set.ncard_coe_finset] at hle
  simpa [gapCount] using hle

/-- Counting core: cluster primes up to `x` are at most ten plus the three prime-pair counts at
gaps `2, 4, 6`. Nothing analytic here. -/
private theorem cluster_count_core (x : ℕ) :
    ({p : ℕ | IsClusterPrime p} ∩ Set.Iic x).ncard ≤
      10 + (gapCount 2 x + gapCount 4 x + gapCount 6 x) := by
  classical
  have hsub : {p : ℕ | IsClusterPrime p} ∩ Set.Iic x ⊆
      (Set.Iic 9 : Set ℕ) ∪ (S x 2 ∪ (S x 4 ∪ S x 6)) := by
    intro p hp
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iic] at hp
    obtain ⟨hcl, hpx⟩ := hp
    rcases Nat.lt_or_ge 9 p with h | h
    · have hodd : Odd p := hcl.1.odd_of_ne_two (by omega)
      rcases prime_near_of_cluster hcl hodd h with h2 | h4 | h6
      · exact Or.inr (Or.inl ⟨⟨hcl.1, h2, h⟩, hpx⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨⟨hcl.1, h4, h⟩, hpx⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨⟨hcl.1, h6, h⟩, hpx⟩))
    · exact Or.inl h
  have hfin : ∀ d, (S x d).Finite := fun d => Set.Finite.subset (Set.finite_Iic x) Set.inter_subset_right
  have h1 : ({p : ℕ | IsClusterPrime p} ∩ Set.Iic x).ncard ≤
      ((Set.Iic 9 : Set ℕ) ∪ (S x 2 ∪ (S x 4 ∪ S x 6))).ncard :=
    Set.ncard_le_ncard hsub ((Set.finite_Iic 9).union ((hfin 2).union ((hfin 4).union (hfin 6))))
  have h2 : ((Set.Iic 9 : Set ℕ) ∪ (S x 2 ∪ (S x 4 ∪ S x 6))).ncard ≤
      10 + (S x 2).ncard + (S x 4).ncard + (S x 6).ncard := by
    have a := Set.ncard_union_le (Set.Iic 9 : Set ℕ) (S x 2 ∪ (S x 4 ∪ S x 6))
    have b := Set.ncard_union_le (S x 2) (S x 4 ∪ S x 6)
    have c := Set.ncard_union_le (S x 4) (S x 6)
    have h9 : (Set.Iic 9 : Set ℕ).ncard = 10 := by simp
    omega
  have h3 : (S x 2).ncard ≤ gapCount 2 x := S_ncard_le x 2 (by norm_num) (by norm_num)
  have h4 : (S x 4).ncard ≤ gapCount 4 x := S_ncard_le x 4 (by norm_num) (by norm_num)
  have h6 : (S x 6).ncard ≤ gapCount 6 x := S_ncard_le x 6 (by norm_num) (by norm_num)
  omega

/-- `log x ^ 2 ≤ 4 x` for `x ≥ 1`. -/
private lemma log_sq_le (x : ℝ) (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 4 * x := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx0.le]; ring
  have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
  have h3 : Real.log x ≤ 2 * Real.sqrt x := by rw [h1]; linarith
  have h4 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h5 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0.le
  nlinarith [Real.sqrt_nonneg x]

/-- **`route_cluster_count_le` modulo the lab's Brun bound for gaps `2, 4, 6`.** -/
private theorem cluster_count_le_of_gapUpper :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 3 ≤ x →
      (({p : ℕ | IsClusterPrime p} ∩ Set.Iic x).ncard : ℝ) ≤ C * x / Real.log x ^ 2 := by
  classical
  obtain ⟨C2, hC2⟩ := gapUpper 2 ⟨1, by norm_num⟩ (by norm_num)
  obtain ⟨C4, hC4⟩ := gapUpper 4 ⟨2, by norm_num⟩ (by norm_num)
  obtain ⟨C6, hC6⟩ := gapUpper 6 ⟨3, by norm_num⟩ (by norm_num)
  have hsp2 := singProd_pos' 2
  have hsp4 := singProd_pos' 4
  have hsp6 := singProd_pos' 6
  set K : ℝ := |C2| * singProd 2 + |C4| * singProd 4 + |C6| * singProd 6 with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    have h1 : (0:ℝ) ≤ |C2| * singProd 2 := mul_nonneg (abs_nonneg C2) hsp2.le
    have h2 : (0:ℝ) ≤ |C4| * singProd 4 := mul_nonneg (abs_nonneg C4) hsp4.le
    have h3 : (0:ℝ) ≤ |C6| * singProd 6 := mul_nonneg (abs_nonneg C6) hsp6.le
    linarith
  refine ⟨K + 40, by linarith, ?_⟩
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlogx : 0 < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hlog : 0 < Real.log x ^ 2 := by positivity
  set q : ℝ := (x : ℝ) / Real.log x ^ 2 with hq
  have hq0 : 0 ≤ q := by positivity
  have hq4 : (1 : ℝ) / 4 ≤ q := by
    have h : (1 : ℝ) / 4 * Real.log x ^ 2 ≤ x := by
      nlinarith [log_sq_le x hx1]
    exact (le_div_iff₀ hlog).mpr h
  have hcore : (({p : ℕ | IsClusterPrime p} ∩ Set.Iic x).ncard : ℝ) ≤
      10 + ((gapCount 2 x : ℝ) + (gapCount 4 x : ℝ) + (gapCount 6 x : ℝ)) := by
    have hnat := cluster_count_core x
    have hR : (({p : ℕ | IsClusterPrime p} ∩ Set.Iic x).ncard : ℝ) ≤
        ((10 + (gapCount 2 x + gapCount 4 x + gapCount 6 x) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at hR
    linarith
  have hgc2 : (gapCount 2 x : ℝ) ≤ C2 * singProd 2 * q := by
    have e : C2 * singProd 2 * (x : ℝ) / Real.log x ^ 2 = C2 * singProd 2 * q := by
      rw [hq]; ring
    rw [← e]; exact hC2 x (by omega)
  have hgc4 : (gapCount 4 x : ℝ) ≤ C4 * singProd 4 * q := by
    have e : C4 * singProd 4 * (x : ℝ) / Real.log x ^ 2 = C4 * singProd 4 * q := by
      rw [hq]; ring
    rw [← e]; exact hC4 x (by omega)
  have hgc6 : (gapCount 6 x : ℝ) ≤ C6 * singProd 6 * q := by
    have e : C6 * singProd 6 * (x : ℝ) / Real.log x ^ 2 = C6 * singProd 6 * q := by
      rw [hq]; ring
    rw [← e]; exact hC6 x (by omega)
  have hKge : C2 * singProd 2 + C4 * singProd 4 + C6 * singProd 6 ≤ K := by
    have h1 : C2 * singProd 2 ≤ |C2| * singProd 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self C2) hsp2.le
    have h2 : C4 * singProd 4 ≤ |C4| * singProd 4 :=
      mul_le_mul_of_nonneg_right (le_abs_self C4) hsp4.le
    have h3 : C6 * singProd 6 ≤ |C6| * singProd 6 :=
      mul_le_mul_of_nonneg_right (le_abs_self C6) hsp6.le
    rw [hK]; linarith
  have hKq : (C2 * singProd 2 + C4 * singProd 4 + C6 * singProd 6) * q ≤ K * q :=
    mul_le_mul_of_nonneg_right hKge hq0
  have h40 : (10 : ℝ) ≤ 40 * q := by linarith
  have hgoal : (K + 40) * (x : ℝ) / Real.log x ^ 2 = (K + 40) * q := by
    rw [hq]; ring
  rw [hgoal]
  nlinarith [hcore, hgc2, hgc4, hgc6, hKq, h40]
end

/-- Unit U-1603, route lemma, PROVED, a Lean proof of a KNOWN result. Plain math: at most
`C x / (log x)^2` cluster primes lie below `x`, from `prime_near_of_cluster` and the lab's Brun bound
`BrunGap.gapUpper` at gaps 2, 4, 6. It is the case `A = 2` of the published bound of Blecksmith,
Erdős and Selfridge [BES99], `≪_A x / (log x)^A` for every `A > 0`, carried by FC as
`erdos_17.variants.upper_BES`, and Elsholtz [El03] is stronger still. `IsClusterPrime` is vacuously
true at `p = 2`, so 2 is counted, which is harmless for an upper bound; OEIS A038133 lists the odd
non-cluster primes, from 97. It points away from infinitely many, so it bounds the problem, not
solves it. -/
theorem route_cluster_count_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 3 ≤ x →
      (({p : ℕ | IsClusterPrime p} ∩ Set.Iic x).ncard : ℝ) ≤ C * x / Real.log x ^ 2 :=
  cluster_count_le_of_gapUpper

end LeanLab.OpenProblems

#print axioms LeanLab.OpenProblems.route_erdos9A_infinite
#print axioms LeanLab.OpenProblems.route_lemoine_positive_density
#print axioms LeanLab.OpenProblems.route_cluster_count_le

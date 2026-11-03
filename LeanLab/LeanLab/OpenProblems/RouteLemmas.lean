import LeanLab.OpenProblems.Erdos9
import LeanLab.OpenProblems.Lemoine
import LeanLab.OpenProblems.Erdos17

/-!
# OpenProblems, named route lemmas for the provers

Unit U-1603, 2026-11-02. AI wrote the Lean code. Each statement below is a named route lemma with
sorry, NOT PROVED. The sealed open problems themselves are `def`s in their own files, and
`MOUNTAIN.md` only lists theorems with a sorry, so these rows are how the provers find this
folder. None of these lemmas settles its open problem. Each one is expected to be true and
weaker than the problem, and closing one is a step, not a solution. Erdős 273 has no row here:
its target is a search winner fed to `Erdos273.statement_of_check`.
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


/-- Unit U-1603, route lemma, OPEN in the lab. Plain math: infinitely many odd numbers are not a
prime plus two powers of 2. The site's page for Erdős 9 credits this to Schinzel, and FC tags it
solved with an outside Lean proof whose body module was not read here. A first step of Erdős 9,
far weaker than positive upper density. -/
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



/-- Unit U-1603, route lemma, OPEN in the lab. Plain math: the odd numbers of the form `p + 2 q`
have positive lower density, the Lemoine twin of the lab's `S3_positive_lower_density` in
`SchnirelmannGoldbach`. Prior art not searched. Far weaker than Lemoine's conjecture. -/
theorem route_lemoine_positive_density :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      c * N ≤ (({n : ℕ | Odd n ∧ IsLemoine n} ∩ Set.Iic N).ncard : ℝ) := by
  sorry

/-! ### Montgomery large-sieve support (private copy) and the cluster-prime count

`PNTPort/LargeSieve/` proves `twin_upper_montgomery`, an explicit upper bound for the number of
prime pairs with difference `2`, but it is outside this file's frozen import closure, so the chain
it rests on (`Basic`, `Dual`, `Farey`, `Parseval`, `PrimeSieve`, `Montgomery`, `MontgomeryBT`,
`MontgomeryAP`, `MontgomeryTau`, `MontgomeryGoldbach`) is copied here privately, followed by
`pair_upper_montgomery`, the same Montgomery sieve for an even difference `d` with the two
forbidden classes `0` and `-d`. Nothing above this comment is changed. -/
end LeanLab.OpenProblems

namespace LeanLab.PNTPort.LargeSieve
/-! ### copied from PNTPort/LargeSieve/Basic.lean -/
section

/-!
# The analytic large sieve inequality

Lab proof, unit U-5000. AI wrote this file. Known mathematics, a weak constant form of the
large sieve of Linnik, Renyi, Roth, Bombieri, Davenport and Halberstam. No cited input.

For points `α r`, `r ∈ s`, pairwise at distance at least `δ` modulo one, and any complex
`a n` on `M < n ≤ M + N`,

  `∑ r, ‖∑ n, a n e(n α r)‖² ≤ (N + 2/δ) ∑ n, ‖a n‖²`.

The proof is the dual form with a Fejer type majorant: average the interval sum over `L`
shifts of a longer interval, so the kernel is a product of two geometric sums, each at most
`1/(2‖θ‖)`; then sum `1/‖θ‖²` over the spaced points by an injective floor map. The sharp
constant `N - 1 + 1/δ` is not needed for Bombieri-Vinogradov type uses.
-/


open Complex Finset Real

/-- `e x = exp(2πix)`. -/
private noncomputable def e (x : ℝ) : ℂ := Complex.exp (I * ((2 * π * x : ℝ) : ℂ))

/-- Distance from `x` to the nearest integer. -/
private noncomputable def dist0 (x : ℝ) : ℝ := |x - round x|

private lemma dist0_nonneg (x : ℝ) : 0 ≤ dist0 x := abs_nonneg _

private lemma dist0_le_half (x : ℝ) : dist0 x ≤ 1 / 2 := abs_sub_round x

private lemma dist0_le_abs_sub_int (x : ℝ) (z : ℤ) : dist0 x ≤ |x - z| := round_le x z

private lemma dist0_neg (x : ℝ) : dist0 (-x) = dist0 x := by
  apply le_antisymm
  · have := dist0_le_abs_sub_int (-x) (-round x)
    rw [show (-x - ((-round x : ℤ) : ℝ)) = -(x - round x) by push_cast; ring, abs_neg] at this
    exact this
  · have := dist0_le_abs_sub_int x (-round (-x))
    rw [show (x - ((-round (-x) : ℤ) : ℝ)) = -(-x - round (-x)) by push_cast; ring,
      abs_neg] at this
    exact this

private lemma dist0_sub_comm (x y : ℝ) : dist0 (x - y) = dist0 (y - x) := by
  rw [← dist0_neg, neg_sub]

private lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma e_zero : e 0 = 1 := by simp [e]

private lemma e_neg (x : ℝ) : e (-x) = (starRingEnd ℂ) (e x) := by
  unfold e
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  push_cast
  ring

private lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma e_int (z : ℤ) : e z = 1 := by
  unfold e
  rw [show I * ((2 * π * (z : ℝ) : ℝ) : ℂ) = (z : ℂ) * (2 * π * I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I z

private lemma e_sub_round (x : ℝ) : e (x - round x) = e x := by
  rw [sub_eq_add_neg, e_add, show (-(round x : ℝ)) = ((-round x : ℤ) : ℝ) by push_cast; ring,
    e_int, mul_one]

private lemma e_nat_mul (k : ℕ) (x : ℝ) : e (k * x) = e x ^ k := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `|sin(πt)| ≥ 2|t|` for `|t| ≤ 1/2`. -/
private lemma two_abs_le_abs_sin {t : ℝ} (ht : |t| ≤ 1 / 2) : 2 * |t| ≤ |Real.sin (π * t)| := by
  have key : ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 2 → 2 * u ≤ Real.sin (π * u) := by
    intro u hu0 hu1
    have h1 := Real.mul_le_sin (x := π * u) (by positivity) (by nlinarith [Real.pi_pos])
    have : 2 / π * (π * u) = 2 * u := by field_simp
    linarith
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h] at ht ⊢
    exact (key t h ht).trans (le_abs_self _)
  · rw [abs_of_neg h] at ht ⊢
    have := key (-t) (by linarith) ht
    rw [show π * -t = -(π * t) by ring, Real.sin_neg] at this
    exact this.trans (neg_le_abs _)

private lemma four_dist0_le (θ : ℝ) : 4 * dist0 θ ≤ ‖e θ - 1‖ := by
  rw [← e_sub_round]
  set t := θ - round θ with ht
  have hb : |t| ≤ 1 / 2 := abs_sub_round θ
  unfold e
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_two]
  have := two_abs_le_abs_sin hb
  rw [show 2 * π * t / 2 = π * t by ring]
  unfold dist0
  rw [← ht]
  linarith

/-- The geometric sum bound `|∑_{k<m} e(kθ)| ≤ 1/(2‖θ‖)`. -/
private lemma norm_geom_le (m : ℕ) {θ : ℝ} (h : 0 < dist0 θ) :
    ‖∑ k ∈ range m, e (k * θ)‖ ≤ 1 / (2 * dist0 θ) := by
  have hpos : 0 < ‖e θ - 1‖ := lt_of_lt_of_le (by linarith) (four_dist0_le θ)
  have hne : e θ ≠ 1 := by
    intro h1; rw [h1, sub_self, norm_zero] at hpos; exact lt_irrefl _ hpos
  simp_rw [e_nat_mul]
  rw [geom_sum_eq hne, norm_div]
  have hnum : ‖e θ ^ m - 1‖ ≤ 2 := by
    calc ‖e θ ^ m - 1‖ ≤ ‖e θ ^ m‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_e, one_pow, norm_one]; norm_num
  calc ‖e θ ^ m - 1‖ / ‖e θ - 1‖ ≤ 2 / ‖e θ - 1‖ :=
        div_le_div_of_nonneg_right hnum hpos.le
    _ ≤ 2 / (4 * dist0 θ) := div_le_div_of_nonneg_left (by norm_num) (by linarith)
        (four_dist0_le θ)
    _ = 1 / (2 * dist0 θ) := by field_simp; ring

/-- Sum of `1/t²` over a `δ`-separated set of reals that are at least `δ`. -/
private lemma sum_inv_sq_sep {ι : Type*} (T : Finset ι) (t : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ i ∈ T, δ ≤ t i)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → δ ≤ |t i - t j|) :
    ∑ i ∈ T, 1 / t i ^ 2 ≤ 2 / δ ^ 2 := by
  set k : ι → ℕ := fun i => ⌊t i / δ⌋₊ with hk
  have hk1 : ∀ i ∈ T, 1 ≤ k i := by
    intro i hi
    exact Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hδ, one_mul]; exact hpos i hi)
  have hkle : ∀ i ∈ T, (k i : ℝ) * δ ≤ t i := by
    intro i hi
    have := Nat.floor_le (div_nonneg (hδ.le.trans (hpos i hi)) hδ.le)
    exact (le_div_iff₀ hδ).1 this
  have hinj : Set.InjOn k T := by
    intro i hi j hj hij
    by_contra hne
    have hs := hsep i hi j hj hne
    have hi0 : 0 ≤ t i / δ := div_nonneg (hδ.le.trans (hpos i hi)) hδ.le
    have hj0 : 0 ≤ t j / δ := div_nonneg (hδ.le.trans (hpos j hj)) hδ.le
    have a1 := Nat.floor_le hi0
    have a2 := Nat.lt_floor_add_one (t i / δ)
    have b1 := Nat.floor_le hj0
    have b2 := Nat.lt_floor_add_one (t j / δ)
    have hij' : (⌊t i / δ⌋₊ : ℝ) = ⌊t j / δ⌋₊ := by exact_mod_cast hij
    have : |t i / δ - t j / δ| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at this
    linarith
  have step1 : ∑ i ∈ T, 1 / t i ^ 2 ≤ ∑ i ∈ T, (1 / δ ^ 2) * (((k i : ℕ) : ℝ) ^ 2)⁻¹ := by
    apply sum_le_sum
    intro i hi
    have hk0 : (0 : ℝ) < k i := by exact_mod_cast hk1 i hi
    rw [← one_div, one_div_mul_one_div, ← mul_pow, mul_comm δ]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ (by positivity) (hkle i hi) 2
  have step2 : ∑ i ∈ T, (((k i : ℕ) : ℝ) ^ 2)⁻¹ = ∑ j ∈ T.image k, ((j : ℝ) ^ 2)⁻¹ :=
    (sum_image (f := fun j : ℕ => ((j : ℝ) ^ 2)⁻¹) hinj).symm
  set K := (T.image k).sup id
  have hsub : T.image k ⊆ Ioo 0 (K + 1) := by
    intro j hj
    rw [mem_Ioo]
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hj
    exact ⟨hk1 i hi, Nat.lt_succ_of_le (le_sup (f := id) hj)⟩
  have step3 : ∑ j ∈ T.image k, ((j : ℝ) ^ 2)⁻¹ ≤ ∑ j ∈ Ioo 0 (K + 1), ((j : ℝ) ^ 2)⁻¹ :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have step4 := sum_Ioo_inv_sq_le (α := ℝ) 0 (K + 1)
  rw [← mul_sum, step2] at step1
  calc ∑ i ∈ T, 1 / t i ^ 2 ≤ 1 / δ ^ 2 * ∑ j ∈ T.image k, ((j : ℝ) ^ 2)⁻¹ := step1
    _ ≤ 1 / δ ^ 2 * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : (2 : ℝ) / ((0 : ℕ) + 1) = 2 := by norm_num
        linarith
    _ = 2 / δ ^ 2 := by ring

/-- Points pairwise at distance at least `δ` modulo one. -/
private def Spaced {ι : Type*} (s : Finset ι) (α : ι → ℝ) (δ : ℝ) : Prop :=
  ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → δ ≤ dist0 (α r - α r')

/-- For `δ`-spaced points, `∑_{r' ≠ r} 1/‖α r - α r'‖² ≤ 4/δ²`. -/
private lemma sum_off_diag {ι : Type*} [DecidableEq ι] {s : Finset ι} {α : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hs : Spaced s α δ) {r : ι} (hr : r ∈ s) :
    ∑ r' ∈ s.erase r, 1 / dist0 (α r - α r') ^ 2 ≤ 4 / δ ^ 2 := by
  set t : ι → ℝ := fun r' => α r' - α r - round (α r' - α r) with ht
  have hdt : ∀ r', dist0 (α r - α r') = |t r'| := by
    intro r'; rw [dist0_sub_comm]; rfl
  have hge : ∀ r' ∈ s.erase r, δ ≤ |t r'| := by
    intro r' hr'
    rw [← hdt]
    exact hs r hr r' (mem_of_mem_erase hr') (ne_of_mem_erase hr').symm
  have hsep : ∀ r1 ∈ s.erase r, ∀ r2 ∈ s.erase r, r1 ≠ r2 → δ ≤ |t r1 - t r2| := by
    intro r1 h1 r2 h2 hne
    have := hs r1 (mem_of_mem_erase h1) r2 (mem_of_mem_erase h2) hne
    refine this.trans ?_
    have h := dist0_le_abs_sub_int (α r1 - α r2)
      (round (α r1 - α r) - round (α r2 - α r))
    convert h using 2
    simp only [ht]
    push_cast
    ring
  rw [← sum_filter_add_sum_filter_not (s.erase r) (fun r' => 0 < t r')]
  have hP : ∑ r' ∈ (s.erase r).filter (fun r' => 0 < t r'), 1 / dist0 (α r - α r') ^ 2
      ≤ 2 / δ ^ 2 := by
    have := sum_inv_sq_sep ((s.erase r).filter (fun r' => 0 < t r')) t hδ
      (by
        intro i hi
        rw [mem_filter] at hi
        have := hge i hi.1
        rwa [abs_of_pos hi.2] at this)
      (by
        intro i hi j hj hne
        exact hsep i (mem_filter.1 hi).1 j (mem_filter.1 hj).1 hne)
    refine le_of_eq_of_le (sum_congr rfl ?_) this
    intro i hi
    rw [hdt, sq_abs]
  have hN : ∑ r' ∈ (s.erase r).filter (fun r' => ¬ 0 < t r'), 1 / dist0 (α r - α r') ^ 2
      ≤ 2 / δ ^ 2 := by
    have := sum_inv_sq_sep ((s.erase r).filter (fun r' => ¬ 0 < t r')) (fun r' => -t r') hδ
      (by
        intro i hi
        rw [mem_filter] at hi
        have h1 := hge i hi.1
        have h2 : t i ≤ 0 := not_lt.1 hi.2
        rw [abs_of_nonpos h2] at h1
        exact h1)
      (by
        intro i hi j hj hne
        have := hsep i (mem_filter.1 hi).1 j (mem_filter.1 hj).1 hne
        rwa [show -t i - -t j = -(t i - t j) by ring, abs_neg])
    refine le_of_eq_of_le (sum_congr rfl ?_) this
    intro i hi
    rw [hdt, sq_abs, neg_sq]
  calc _ ≤ 2 / δ ^ 2 + 2 / δ ^ 2 := add_le_add hP hN
    _ = 4 / δ ^ 2 := by ring


end

/-! ### copied from PNTPort/LargeSieve/Dual.lean -/
section

/-!
# The large sieve inequality, dual form and main form

Lab proof, unit U-5000. AI wrote this file. Known mathematics, no cited input.

* `dual_large_sieve`: `∑_{M<n≤M+N} ‖∑_r b_r e(n α_r)‖² ≤ (N + 2/δ) ∑_r ‖b_r‖²`.
* `large_sieve`: `∑_r ‖∑_{M<n≤M+N} a_n e(n α_r)‖² ≤ (N + 2/δ) ∑_n ‖a_n‖²`.

Both for points `α_r` that are `δ`-spaced modulo one, `Spaced s α δ`, with `δ > 0`.
-/


open Complex Finset Real

variable {ι : Type*} [DecidableEq ι]

/-- The dual sum `B(n) = ∑_r b_r e(n α_r)`. -/
private noncomputable def dualSum (s : Finset ι) (α : ι → ℝ) (b : ι → ℂ) (n : ℤ) : ℂ :=
  ∑ r ∈ s, b r * e (n * α r)

omit [DecidableEq ι] in
private lemma normSq_dualSum (s : Finset ι) (α : ι → ℝ) (b : ι → ℂ) (n : ℤ) :
    ((‖dualSum s α b n‖ ^ 2 : ℝ) : ℂ) =
      ∑ r ∈ s, ∑ r' ∈ s, b r * (starRingEnd ℂ) (b r') * e (n * (α r - α r')) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  unfold dualSum
  rw [map_sum, sum_mul_sum]
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro r' _
  rw [map_mul, ← e_neg, show (n : ℝ) * (α r - α r') = n * α r + -(n * α r') by ring, e_add]
  ring

/-- The geometric sum `G m θ = ∑_{k<m} e(kθ)`. -/
private noncomputable def G (m : ℕ) (θ : ℝ) : ℂ := ∑ k ∈ range m, e (k * θ)

private lemma G_zero (m : ℕ) : G m 0 = m := by simp [G, e_zero]

private lemma shifted_kernel (c : ℤ) (L P : ℕ) (θ : ℝ) :
    ∑ u ∈ range L, ∑ v ∈ range P, e (((c + u + v : ℤ) : ℝ) * θ) =
      e (c * θ) * (G L θ * G P θ) := by
  rw [G, G, sum_mul_sum, mul_sum]
  apply sum_congr rfl
  intro u _
  rw [mul_sum]
  apply sum_congr rfl
  intro v _
  push_cast
  rw [add_mul, add_mul, e_add, e_add]
  ring

private lemma norm_shifted_kernel_le (c : ℤ) (L P : ℕ) {θ : ℝ} (hθ : 0 < dist0 θ) :
    ‖∑ u ∈ range L, ∑ v ∈ range P, e (((c + u + v : ℤ) : ℝ) * θ)‖ ≤
      1 / (4 * dist0 θ ^ 2) := by
  rw [shifted_kernel, norm_mul, norm_e, one_mul, norm_mul]
  calc ‖G L θ‖ * ‖G P θ‖ ≤ (1 / (2 * dist0 θ)) * (1 / (2 * dist0 θ)) :=
        mul_le_mul (norm_geom_le L hθ) (norm_geom_le P hθ) (norm_nonneg _) (by positivity)
    _ = 1 / (4 * dist0 θ ^ 2) := by field_simp; ring

omit [DecidableEq ι] in
/-- `∑∑ x_r x_r' K r r' ≤ ∑ x_r² ∑ K r r'` for a symmetric nonnegative kernel. -/
private lemma sum_sum_mul_le (s : Finset ι) (x : ι → ℝ) (K : ι → ι → ℝ)
    (hK : ∀ r r', 0 ≤ K r r') (hsym : ∀ r r', K r r' = K r' r) :
    ∑ r ∈ s, ∑ r' ∈ s, x r * x r' * K r r' ≤ ∑ r ∈ s, x r ^ 2 * ∑ r' ∈ s, K r r' := by
  have h1 : ∑ r ∈ s, ∑ r' ∈ s, x r * x r' * K r r' ≤
      ∑ r ∈ s, ∑ r' ∈ s, ((1 / 2) * (x r ^ 2 * K r r') + (1 / 2) * (x r' ^ 2 * K r r')) := by
    apply sum_le_sum; intro r _; apply sum_le_sum; intro r' _
    have := hK r r'
    nlinarith [sq_nonneg (x r - x r'), mul_nonneg this (sq_nonneg (x r - x r'))]
  have h2 : ∑ r ∈ s, ∑ r' ∈ s, x r' ^ 2 * K r r' = ∑ r ∈ s, ∑ r' ∈ s, x r ^ 2 * K r r' := by
    rw [sum_comm]
    apply sum_congr rfl; intro r _; apply sum_congr rfl; intro r' _
    rw [hsym]
  have h3 : ∑ r ∈ s, ∑ r' ∈ s, ((1 / 2) * (x r ^ 2 * K r r') + (1 / 2) * (x r' ^ 2 * K r r'))
      = (1 / 2) * ∑ r ∈ s, ∑ r' ∈ s, x r ^ 2 * K r r' +
        (1 / 2) * ∑ r ∈ s, ∑ r' ∈ s, x r' ^ 2 * K r r' := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro r _
    rw [mul_sum, mul_sum, ← sum_add_distrib]
  rw [h3, h2] at h1
  refine h1.trans (le_of_eq ?_)
  rw [← add_mul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_mul]
  apply sum_congr rfl; intro r _
  rw [mul_sum]

/-- The averaged shifted sum, bounded by the kernel computation. -/
private lemma shifted_bound {s : Finset ι} {α : ι → ℝ} {δ : ℝ} (hδ : 0 < δ) (hs : Spaced s α δ)
    (b : ι → ℂ) (c : ℤ) (L P : ℕ) :
    ∑ u ∈ range L, ∑ v ∈ range P, ‖dualSum s α b (c + u + v)‖ ^ 2 ≤
      (L * P + 1 / δ ^ 2) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  set Kc : ι → ι → ℂ := fun r r' =>
    ∑ u ∈ range L, ∑ v ∈ range P, e (((c + u + v : ℤ) : ℝ) * (α r - α r')) with hKc
  set X := ∑ u ∈ range L, ∑ v ∈ range P, ‖dualSum s α b (c + u + v)‖ ^ 2 with hXdef
  have hX : (X : ℂ) = ∑ r ∈ s, ∑ r' ∈ s, b r * (starRingEnd ℂ) (b r') * Kc r r' := by
    rw [hXdef]
    simp_rw [Complex.ofReal_sum, normSq_dualSum]
    calc _ = ∑ u ∈ range L, ∑ r ∈ s, ∑ v ∈ range P, ∑ r' ∈ s,
          b r * (starRingEnd ℂ) (b r') * e (((c + u + v : ℤ) : ℝ) * (α r - α r')) :=
          sum_congr rfl (fun u _ => sum_comm)
      _ = ∑ u ∈ range L, ∑ r ∈ s, ∑ r' ∈ s, ∑ v ∈ range P,
          b r * (starRingEnd ℂ) (b r') * e (((c + u + v : ℤ) : ℝ) * (α r - α r')) :=
          sum_congr rfl (fun u _ => sum_congr rfl (fun r _ => sum_comm))
      _ = ∑ r ∈ s, ∑ u ∈ range L, ∑ r' ∈ s, ∑ v ∈ range P,
          b r * (starRingEnd ℂ) (b r') * e (((c + u + v : ℤ) : ℝ) * (α r - α r')) := sum_comm
      _ = ∑ r ∈ s, ∑ r' ∈ s, ∑ u ∈ range L, ∑ v ∈ range P,
          b r * (starRingEnd ℂ) (b r') * e (((c + u + v : ℤ) : ℝ) * (α r - α r')) :=
          sum_congr rfl (fun r _ => sum_comm)
      _ = _ := by
          apply sum_congr rfl; intro r _; apply sum_congr rfl; intro r' _
          rw [hKc, mul_sum]
          apply sum_congr rfl; intro u _
          rw [mul_sum]
  set Kb : ι → ι → ℝ := fun r r' =>
    if r = r' then (L * P : ℝ) else 1 / (4 * dist0 (α r - α r') ^ 2) with hKb
  have hKb0 : ∀ r r', 0 ≤ Kb r r' := by
    intro r r'; simp only [hKb]; split_ifs <;> positivity
  have hKbsym : ∀ r r', Kb r r' = Kb r' r := by
    intro r r'
    simp only [hKb]
    by_cases h : r = r'
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), dist0_sub_comm]
  have hKle : ∀ r ∈ s, ∀ r' ∈ s, ‖Kc r r'‖ ≤ Kb r r' := by
    intro r hr r' hr'
    by_cases h : r = r'
    · subst h
      simp only [hKc, hKb, if_pos rfl, sub_self, mul_zero, e_zero, sum_const, card_range,
        nsmul_eq_mul, mul_one]
      rw [norm_mul]
      simp
    · simp only [hKb, if_neg h]
      exact norm_shifted_kernel_le c L P (lt_of_lt_of_le hδ (hs r hr r' hr' h))
  have hX0 : 0 ≤ X := sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => by positivity))
  have step1 : X ≤ ∑ r ∈ s, ∑ r' ∈ s, ‖b r‖ * ‖b r'‖ * Kb r r' := by
    have : X = ‖(X : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX0]
    rw [this, hX]
    refine (norm_sum_le _ _).trans (sum_le_sum (fun r hr => (norm_sum_le _ _).trans
      (sum_le_sum (fun r' hr' => ?_))))
    rw [norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (hKle r hr r' hr') (by positivity)
  have step2 := sum_sum_mul_le s (fun r => ‖b r‖) Kb hKb0 hKbsym
  have step3 : ∀ r ∈ s, ∑ r' ∈ s, Kb r r' ≤ L * P + 1 / δ ^ 2 := by
    intro r hr
    rw [← add_sum_erase s _ hr]
    simp only [hKb, if_pos rfl]
    refine add_le_add le_rfl ?_
    have hoff := sum_off_diag hδ hs hr
    calc ∑ x ∈ s.erase r, (if r = x then (L * P : ℝ) else 1 / (4 * dist0 (α r - α x) ^ 2))
        = ∑ x ∈ s.erase r, (1 / 4) * (1 / dist0 (α r - α x) ^ 2) := by
          apply sum_congr rfl; intro x hx
          rw [if_neg (ne_of_mem_erase hx).symm]
          field_simp
      _ = (1 / 4) * ∑ x ∈ s.erase r, 1 / dist0 (α r - α x) ^ 2 := by rw [mul_sum]
      _ ≤ (1 / 4) * (4 / δ ^ 2) := by linarith
      _ = 1 / δ ^ 2 := by ring
  calc X ≤ _ := step1
    _ ≤ ∑ r ∈ s, ‖b r‖ ^ 2 * ∑ r' ∈ s, Kb r r' := step2
    _ ≤ ∑ r ∈ s, ‖b r‖ ^ 2 * (L * P + 1 / δ ^ 2) :=
        sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (step3 r hr) (by positivity))
    _ = (L * P + 1 / δ ^ 2) * ∑ r ∈ s, ‖b r‖ ^ 2 := by rw [← sum_mul, mul_comm]

/-- **Dual large sieve.** -/
private theorem dual_large_sieve {s : Finset ι} {α : ι → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hs : Spaced s α δ) (b : ι → ℂ) (M : ℤ) (N : ℕ) :
    ∑ n ∈ Ioc M (M + N), ‖dualSum s α b n‖ ^ 2 ≤ (N + 2 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  set L : ℕ := ⌈1 / δ⌉₊ with hLdef
  have hinv : 0 < 1 / δ := by positivity
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (by
    rw [hLdef]; exact (Nat.ceil_pos.2 hinv).ne')
  have hLge : 1 / δ ≤ L := Nat.le_ceil _
  have hLlt : (L : ℝ) < 1 / δ + 1 := Nat.ceil_lt_add_one hinv.le
  set P : ℕ := N + L - 1 with hPdef
  set c : ℤ := M + 2 - L with hcdef
  set f : ℤ → ℝ := fun n => ‖dualSum s α b n‖ ^ 2 with hf
  set A := ∑ n ∈ Ioc M (M + N), f n with hA
  have hu : ∀ u ∈ range L, A ≤ ∑ v ∈ range P, f (c + u + v) := by
    intro u hu
    rw [mem_range] at hu
    have hsub : Ioc M (M + N) ⊆ (range P).image (fun v : ℕ => c + u + v) := by
      intro n hn
      rw [mem_Ioc] at hn
      rw [mem_image]
      refine ⟨(n - c - u).toNat, ?_, ?_⟩
      · rw [mem_range]; omega
      · omega
    have hinj : Set.InjOn (fun v : ℕ => c + u + v) (range P) := by
      intro v _ w _ h
      simp only at h
      omega
    calc A ≤ ∑ n ∈ (range P).image (fun v : ℕ => c + u + v), f n :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = ∑ v ∈ range P, f (c + u + v) := sum_image hinj
  have hsum : (L : ℝ) * A ≤ (L * P + 1 / δ ^ 2) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
    calc (L : ℝ) * A = ∑ u ∈ range L, A := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ ∑ u ∈ range L, ∑ v ∈ range P, f (c + u + v) := sum_le_sum hu
      _ ≤ _ := shifted_bound hδ hs b c L P
  have hB0 : 0 ≤ ∑ r ∈ s, ‖b r‖ ^ 2 := sum_nonneg (fun _ _ => by positivity)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hPcast : (P : ℝ) = N + L - 1 := by
    rw [hPdef, Nat.cast_sub (by omega)]; push_cast; ring
  have hconst : (L * P + 1 / δ ^ 2) ≤ L * (N + 2 / δ) := by
    rw [hPcast]
    have h1 : 1 / δ ^ 2 ≤ L * (1 / δ) := by
      rw [show 1 / δ ^ 2 = (1 / δ) * (1 / δ) by ring]
      exact mul_le_mul_of_nonneg_right hLge hinv.le
    have h2 : (L : ℝ) * (L - 1) ≤ L * (1 / δ) :=
      mul_le_mul_of_nonneg_left (by linarith) hLpos.le
    calc (L : ℝ) * (N + L - 1) + 1 / δ ^ 2 = L * N + L * (L - 1) + 1 / δ ^ 2 := by ring
      _ ≤ L * N + L * (1 / δ) + L * (1 / δ) := by linarith
      _ = L * (N + 2 / δ) := by ring
  have : (L : ℝ) * A ≤ L * ((N + 2 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2) := by
    calc (L : ℝ) * A ≤ _ := hsum
      _ ≤ L * (N + 2 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := mul_le_mul_of_nonneg_right hconst hB0
      _ = _ := by ring
  exact le_of_mul_le_mul_left this hLpos

/-- **The large sieve inequality**, constant `N + 2/δ`. -/
private theorem large_sieve {s : Finset ι} {α : ι → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hs : Spaced s α δ) (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ∑ r ∈ s, ‖∑ n ∈ Ioc M (M + N), a n * e (n * α r)‖ ^ 2 ≤
      (N + 2 / δ) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  set I := Ioc M (M + N)
  set S : ι → ℂ := fun r => ∑ n ∈ I, a n * e (n * α r) with hS
  set b : ι → ℂ := fun r => (starRingEnd ℂ) (S r) with hb
  set X := ∑ r ∈ s, ‖S r‖ ^ 2 with hXdef
  have hX0 : 0 ≤ X := sum_nonneg (fun _ _ => by positivity)
  have hX : (X : ℂ) = ∑ n ∈ I, a n * dualSum s α b n := by
    rw [hXdef, Complex.ofReal_sum]
    simp_rw [Complex.ofReal_pow, ← Complex.conj_mul']
    unfold dualSum
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl; intro r _
    rw [hS, mul_sum]
    apply sum_congr rfl; intro n _
    rw [hb]
    ring
  have h1 : X ≤ ∑ n ∈ I, ‖a n‖ * ‖dualSum s α b n‖ := by
    have : X = ‖(X : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX0]
    rw [this, hX]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp_rw [norm_mul]
  have h2 := sum_mul_sq_le_sq_mul_sq I (fun n => ‖a n‖) (fun n => ‖dualSum s α b n‖)
  have h3 := dual_large_sieve hδ hs b M N
  have hbX : ∑ r ∈ s, ‖b r‖ ^ 2 = X := by
    rw [hXdef]; apply sum_congr rfl; intro r _; rw [hb, Complex.norm_conj]
  rw [hbX] at h3
  set Aa := ∑ n ∈ I, ‖a n‖ ^ 2
  have hAa : 0 ≤ Aa := sum_nonneg (fun _ _ => by positivity)
  have hΔ : 0 ≤ (N : ℝ) + 2 / δ := by positivity
  have key : X ^ 2 ≤ Aa * ((N + 2 / δ) * X) := by
    calc X ^ 2 ≤ (∑ n ∈ I, ‖a n‖ * ‖dualSum s α b n‖) ^ 2 := pow_le_pow_left₀ hX0 h1 2
      _ ≤ Aa * ∑ n ∈ I, ‖dualSum s α b n‖ ^ 2 := h2
      _ ≤ Aa * ((N + 2 / δ) * X) := mul_le_mul_of_nonneg_left h3 hAa
  rcases eq_or_lt_of_le hX0 with h | h
  · rw [← h]; positivity
  · have : X * X ≤ X * ((N + 2 / δ) * Aa) := by nlinarith
    exact le_of_mul_le_mul_left this h


end

/-! ### copied from PNTPort/LargeSieve/Farey.lean -/
section

/-!
# The large sieve at Farey fractions

Lab proof, unit U-5000. AI wrote this file. Known mathematics, no cited input.

The reduced fractions `a/q` with `1 ≤ q ≤ Q`, `0 ≤ a < q`, `gcd(a, q) = 1` are `1/Q²`-spaced
modulo one, so

  `∑_{q ≤ Q} ∑_{a mod q, (a,q)=1} ‖∑_{M<n≤M+N} a_n e(n a/q)‖² ≤ (N + 2Q²) ∑_n ‖a_n‖²`.

This is the form used for Bombieri-Vinogradov; the sharp constant is `N - 1 + Q²`.
-/


open Complex Finset Real

/-- The pairs `(q, a)` with `1 ≤ q ≤ Q`, `a < q`, `gcd(a, q) = 1`. -/
private def farey (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 Q) ×ˢ (range Q)).filter (fun p => p.2 < p.1 ∧ Nat.Coprime p.2 p.1)

/-- The fraction `a/q` of a pair `(q, a)`. -/
private noncomputable def fareyPt (p : ℕ × ℕ) : ℝ := (p.2 : ℝ) / p.1

private lemma mem_farey {Q : ℕ} {p : ℕ × ℕ} :
    p ∈ farey Q ↔ 1 ≤ p.1 ∧ p.1 ≤ Q ∧ p.2 < p.1 ∧ Nat.Coprime p.2 p.1 := by
  unfold farey
  rw [mem_filter, mem_product, mem_Icc, mem_range]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, _⟩, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨⟨h1, h2⟩, by omega⟩, h3, h4⟩

/-- Distinct reduced fractions with denominators at most `Q` are `1/Q²` apart mod one. -/
private lemma farey_spaced (Q : ℕ) : Spaced (farey Q) fareyPt (1 / (Q : ℝ) ^ 2) := by
  rintro ⟨q, a⟩ hp ⟨q', a'⟩ hp' hne
  rw [mem_farey] at hp hp'
  obtain ⟨hq1, hqQ, haq, hcop⟩ := hp
  obtain ⟨hq1', hqQ', haq', hcop'⟩ := hp'
  simp only at hq1 hqQ haq hcop hq1' hqQ' haq' hcop'
  simp only [fareyPt]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqpos' : (0 : ℝ) < q' := by exact_mod_cast hq1'
  set m : ℤ := round ((a : ℝ) / q - a' / q') with hm
  set j : ℤ := (a : ℤ) * q' - a' * q - m * q * q' with hj
  have hx : (a : ℝ) / q - a' / q' - m = j / (q * q') := by
    rw [hj]; push_cast; field_simp
  have hj0 : j ≠ 0 := by
    intro hj0
    rw [hj0, Int.cast_zero, zero_div, sub_eq_zero] at hx
    -- `a/q - a'/q'` is an integer of absolute value below one, hence zero
    have hlt1 : |(a : ℝ) / q - a' / q'| < 1 := by
      have h1 : (a : ℝ) / q < 1 := by
        rw [div_lt_one hqpos]; exact_mod_cast haq
      have h2 : (a' : ℝ) / q' < 1 := by
        rw [div_lt_one hqpos']; exact_mod_cast haq'
      have h3 : 0 ≤ (a : ℝ) / q := by positivity
      have h4 : 0 ≤ (a' : ℝ) / q' := by positivity
      rw [abs_lt]; constructor <;> linarith
    rw [hx] at hlt1
    have hm0 : m = 0 := by
      have : |(m : ℝ)| < 1 := hlt1
      rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at this
      have := abs_lt.1 this; omega
    rw [hm0, Int.cast_zero, sub_eq_zero, div_eq_div_iff hqpos.ne' hqpos'.ne'] at hx
    have hnat : a * q' = a' * q := by exact_mod_cast hx
    have hd1 : q ∣ q' := by
      have : q ∣ a * q' := ⟨a', by rw [hnat, mul_comm]⟩
      exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left this
    have hd2 : q' ∣ q := by
      have : q' ∣ a' * q := ⟨a, by rw [← hnat, mul_comm]⟩
      exact (Nat.Coprime.symm hcop').dvd_of_dvd_mul_left this
    have hqq : q = q' := Nat.dvd_antisymm hd1 hd2
    subst hqq
    have haa : a = a' := Nat.eq_of_mul_eq_mul_right (by omega) hnat
    exact hne (by rw [haa])
  have hdist : dist0 ((a : ℝ) / q - a' / q') = |(j : ℝ)| / (q * q') := by
    unfold dist0
    rw [← hm, hx, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * q')]
  rw [hdist]
  have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
    rw [← Int.cast_abs, ← Int.cast_one, Int.cast_le]
    exact Int.one_le_abs hj0
  have hQ : (q : ℝ) * q' ≤ (Q : ℝ) ^ 2 := by
    have : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have : (q' : ℝ) ≤ Q := by exact_mod_cast hqQ'
    nlinarith
  calc 1 / (Q : ℝ) ^ 2 ≤ 1 / (q * q') := one_div_le_one_div_of_le (by positivity) hQ
    _ ≤ |(j : ℝ)| / (q * q') := div_le_div_of_nonneg_right hj1 (by positivity)

/-- **The large sieve at Farey fractions**, constant `N + 2Q²`. -/
private theorem farey_large_sieve {Q : ℕ} (hQ : 1 ≤ Q) (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ∑ p ∈ farey Q, ‖∑ n ∈ Ioc M (M + N), a n * e (n * fareyPt p)‖ ^ 2 ≤
      (N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hδ : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
  have := large_sieve hδ (farey_spaced Q) a M N
  rwa [show (2 : ℝ) / (1 / (Q : ℝ) ^ 2) = 2 * (Q : ℝ) ^ 2 by field_simp] at this


end

/-! ### copied from PNTPort/LargeSieve/Parseval.lean -/
section

/-!
# Parseval modulo q and the large sieve over primes

Lab proof, unit U-5000. AI wrote this file. Known mathematics, no cited input.

* `sum_e_mul_div`: `∑_{c<q} e(kc/q)` is `q` if `q ∣ k` and `0` otherwise.
* `parseval_mod`: `∑_{c<q} ‖S(c/q)‖² = q ∑_{b<q} ‖Z(q,b)‖²`, where `Z(q,b)` sums `a_n` over
  `n ≡ b mod q`.
* `prime_large_sieve`: `∑_{p≤Q prime} (p ∑_b ‖Z(p,b)‖² - ‖Z‖²) ≤ (N + 2Q²) ∑ ‖a_n‖²`, the
  prime modulus form of the arithmetic large sieve, Renyi and Gallagher.
-/


open Complex Finset Real

private lemma dist0_eq_zero_iff {x : ℝ} : dist0 x = 0 ↔ x = round x := by
  unfold dist0; rw [abs_eq_zero, sub_eq_zero]

private lemma int_dvd_of_e_eq_one {k : ℤ} {q : ℕ} (hq : 0 < q) (h : e (k / q) = 1) :
    (q : ℤ) ∣ k := by
  have h4 := four_dist0_le ((k : ℝ) / q)
  rw [h, sub_self, norm_zero] at h4
  have h0 : dist0 ((k : ℝ) / q) = 0 := le_antisymm (by linarith) (dist0_nonneg _)
  rw [dist0_eq_zero_iff] at h0
  refine ⟨round ((k : ℝ) / q), ?_⟩
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have : (k : ℝ) = q * round ((k : ℝ) / q) := by
    rw [← h0]; field_simp
  exact_mod_cast this

/-- Orthogonality of additive characters modulo `q`. -/
private lemma sum_e_mul_div (k : ℤ) {q : ℕ} (hq : 0 < q) :
    ∑ c ∈ range q, e (k * c / q) = if (q : ℤ) ∣ k then (q : ℂ) else 0 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  split_ifs with hdvd
  · obtain ⟨t, rfl⟩ := hdvd
    have : ∀ c ∈ range q, e (((q : ℤ) * t : ℤ) * c / q) = 1 := by
      intro c _
      rw [show (((q : ℤ) * t : ℤ) : ℝ) * c / q = ((t * c : ℤ) : ℝ) by
        push_cast; field_simp]
      exact e_int _
    rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul, mul_one]
  · have hne : e (k / q) ≠ 1 := fun h => hdvd (int_dvd_of_e_eq_one hq h)
    have hpow : ∀ c ∈ range q, e (k * c / q) = e (k / q) ^ c := by
      intro c _
      rw [← e_nat_mul]; congr 1; ring
    rw [sum_congr rfl hpow, geom_sum_eq hne, ← e_nat_mul,
      show (q : ℝ) * (k / q) = ((k : ℤ) : ℝ) by field_simp, e_int, sub_self, zero_div]

/-- `‖∑ n, f n‖²` expanded as a double sum. -/
private lemma ofReal_normSq_sum {α : Type*} (I : Finset α) (f : α → ℂ) :
    ((‖∑ n ∈ I, f n‖ ^ 2 : ℝ) : ℂ) = ∑ n ∈ I, ∑ m ∈ I, f n * (starRingEnd ℂ) (f m) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum]

/-- Residue sum `Z(q, b) = ∑_{n ∈ I, n ≡ b mod q} a n`. -/
private noncomputable def resSum (I : Finset ℤ) (a : ℤ → ℂ) (q : ℕ) (b : ℕ) : ℂ :=
  ∑ n ∈ I.filter (fun n => n % (q : ℤ) = b), a n

private lemma sum_res_indicator {q : ℕ} (hq : 0 < q) (n m : ℤ) (F : ℂ) :
    ∑ b ∈ range q, (if n % (q : ℤ) = b ∧ m % (q : ℤ) = b then F else 0) =
      if n % (q : ℤ) = m % (q : ℤ) then F else 0 := by
  have hn0 : 0 ≤ n % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq.ne')
  have hnq : n % (q : ℤ) < q := Int.emod_lt_of_pos _ (by exact_mod_cast hq)
  have : ∀ b ∈ range q, (if n % (q : ℤ) = b ∧ m % (q : ℤ) = b then F else 0) =
      if b = (n % (q : ℤ)).toNat then (if n % (q : ℤ) = m % (q : ℤ) then F else 0) else 0 := by
    intro b _
    by_cases hb : b = (n % (q : ℤ)).toNat
    · have hb' : n % (q : ℤ) = b := by rw [hb]; omega
      rw [if_pos hb]
      by_cases hm : n % (q : ℤ) = m % (q : ℤ)
      · rw [if_pos ⟨hb', hm ▸ hb'⟩, if_pos hm]
      · rw [if_neg hm, if_neg]; rintro ⟨h1, h2⟩; exact hm (h1.trans h2.symm)
    · rw [if_neg hb, if_neg]
      rintro ⟨h1, _⟩; apply hb; omega
  rw [sum_congr rfl this, sum_ite_eq']
  rw [if_pos (by rw [mem_range]; omega)]

/-- **Parseval modulo `q`.** -/
private theorem parseval_mod (I : Finset ℤ) (a : ℤ → ℂ) {q : ℕ} (hq : 0 < q) :
    ∑ c ∈ range q, ‖∑ n ∈ I, a n * e (n * c / q)‖ ^ 2 =
      q * ∑ b ∈ range q, ‖resSum I a q b‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast [Complex.ofReal_sum]
  simp_rw [← Complex.ofReal_pow, ofReal_normSq_sum]
  -- left side
  have hL : ∑ c ∈ range q, ∑ n ∈ I, ∑ m ∈ I,
      a n * e (n * c / q) * (starRingEnd ℂ) (a m * e (m * c / q)) =
      ∑ n ∈ I, ∑ m ∈ I, a n * (starRingEnd ℂ) (a m) *
        (if (q : ℤ) ∣ (n - m) then (q : ℂ) else 0) := by
    rw [sum_comm]
    apply sum_congr rfl; intro n _
    rw [sum_comm]
    apply sum_congr rfl; intro m _
    rw [← sum_e_mul_div (n - m) hq, mul_sum]
    apply sum_congr rfl; intro c _
    rw [map_mul, ← e_neg, show ((n - m : ℤ) : ℝ) * c / q = n * c / q + -(m * c / q) by
      push_cast; ring, e_add]
    ring
  rw [hL]
  -- right side
  unfold resSum
  simp_rw [ofReal_normSq_sum]
  have hR : ∀ b ∈ range q, ∑ n ∈ I.filter (fun n => n % (q : ℤ) = b),
      ∑ m ∈ I.filter (fun n => n % (q : ℤ) = b), a n * (starRingEnd ℂ) (a m) =
      ∑ n ∈ I, ∑ m ∈ I, (if n % (q : ℤ) = b ∧ m % (q : ℤ) = b then
        a n * (starRingEnd ℂ) (a m) else 0) := by
    intro b _
    rw [sum_filter]
    apply sum_congr rfl; intro n _
    rw [sum_filter]
    split_ifs with hn
    · apply sum_congr rfl; intro m _
      by_cases hm : m % (q : ℤ) = b
      · rw [if_pos hm, if_pos ⟨hn, hm⟩]
      · rw [if_neg hm, if_neg (fun h => hm h.2)]
    · symm; apply sum_eq_zero; intro m _; rw [if_neg (fun h => hn h.1)]
  rw [sum_congr rfl hR, mul_sum]
  symm
  calc ∑ b ∈ range q, (q : ℂ) * ∑ n ∈ I, ∑ m ∈ I,
        (if n % (q : ℤ) = b ∧ m % (q : ℤ) = b then a n * (starRingEnd ℂ) (a m) else 0)
      = ∑ n ∈ I, ∑ m ∈ I, (q : ℂ) * ∑ b ∈ range q,
        (if n % (q : ℤ) = b ∧ m % (q : ℤ) = b then a n * (starRingEnd ℂ) (a m) else 0) := by
        simp_rw [mul_sum]
        rw [sum_comm]
        apply sum_congr rfl; intro n _
        rw [sum_comm]
    _ = _ := by
        apply sum_congr rfl; intro n _
        apply sum_congr rfl; intro m _
        rw [sum_res_indicator hq]
        have hiff : (q : ℤ) ∣ (n - m) ↔ n % (q : ℤ) = m % (q : ℤ) := by
          rw [← Int.ModEq, Int.modEq_iff_dvd]
          constructor
          · intro h; rw [show m - n = -(n - m) by ring]; exact (Int.dvd_neg).2 h
          · intro h; rw [show n - m = -(m - n) by ring]; exact (Int.dvd_neg).2 h
        by_cases h : n % (q : ℤ) = m % (q : ℤ)
        · rw [if_pos (hiff.2 h), if_pos h]; ring
        · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]; ring


end

/-! ### copied from PNTPort/LargeSieve/PrimeSieve.lean -/
section

/-!
# The arithmetic large sieve over prime moduli

Lab proof, unit U-5000. AI wrote this file. Known mathematics, Renyi and Gallagher's prime
modulus form, no cited input.

* `prime_large_sieve`: `∑_{p ≤ Q prime} (p ∑_{b<p} ‖Z(p,b)‖² - ‖Z‖²) ≤ (N + 2Q²) ∑ ‖a_n‖²`.
* `sifted_card_bound`: if a finite set `A ⊆ (M, M+N]` meets at most `p - ω p` residue
  classes modulo each prime `p ≤ Q`, with `ω p < p`, then
  `|A| ∑_{p ≤ Q prime} ω p / (p - ω p) ≤ N + 2Q²`.
-/


open Complex Finset Real

/-- The primes up to `Q`. -/
private def primesUpTo (Q : ℕ) : Finset ℕ := (Icc 1 Q).filter Nat.Prime

private lemma parseval_sub_zero (I : Finset ℤ) (a : ℤ → ℂ) {q : ℕ} (hq : 0 < q) :
    q * ∑ b ∈ range q, ‖resSum I a q b‖ ^ 2 - ‖∑ n ∈ I, a n‖ ^ 2 =
      ∑ c ∈ Ico 1 q, ‖∑ n ∈ I, a n * e (n * fareyPt (q, c))‖ ^ 2 := by
  rw [← parseval_mod I a hq, range_eq_Ico, sum_eq_sum_Ico_succ_bot hq]
  simp only [Nat.cast_zero, mul_zero, zero_div, e_zero, mul_one, add_sub_cancel_left, fareyPt]
  apply sum_congr rfl; intro c _
  simp_rw [mul_div_assoc]

/-- **The prime modulus large sieve.** -/
private theorem prime_large_sieve {Q : ℕ} (hQ : 1 ≤ Q) (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ∑ p ∈ primesUpTo Q, ((p : ℝ) * ∑ b ∈ range p, ‖resSum (Ioc M (M + N)) a p b‖ ^ 2 -
        ‖∑ n ∈ Ioc M (M + N), a n‖ ^ 2) ≤
      (N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  set I := Ioc M (M + N)
  set f : ℕ × ℕ → ℝ := fun x => ‖∑ n ∈ I, a n * e (n * fareyPt x)‖ ^ 2 with hf
  have hprime : ∀ p ∈ primesUpTo Q, p.Prime := fun p hp => (mem_filter.1 hp).2
  have h1 : ∑ p ∈ primesUpTo Q, ((p : ℝ) * ∑ b ∈ range p, ‖resSum I a p b‖ ^ 2 -
      ‖∑ n ∈ I, a n‖ ^ 2) = ∑ p ∈ primesUpTo Q, ∑ c ∈ Ico 1 p, f (p, c) :=
    sum_congr rfl (fun p hp => parseval_sub_zero I a (hprime p hp).pos)
  set T : Finset (ℕ × ℕ) := (primesUpTo Q).biUnion
    (fun p => (Ico 1 p).map ⟨fun c => (p, c), fun c c' h => by simpa using h⟩) with hT
  have h2 : ∑ p ∈ primesUpTo Q, ∑ c ∈ Ico 1 p, f (p, c) = ∑ x ∈ T, f x := by
    rw [hT, sum_biUnion]
    · apply sum_congr rfl; intro p _; rw [sum_map]; rfl
    · intro p _ p' _ hne
      refine disjoint_left.2 ?_
      intro x hx hx'
      rw [mem_map] at hx hx'
      obtain ⟨c, _, rfl⟩ := hx
      obtain ⟨c', _, h⟩ := hx'
      exact hne (congrArg Prod.fst h).symm
  have hsub : T ⊆ farey Q := by
    intro x hx
    rw [hT, mem_biUnion] at hx
    obtain ⟨p, hp, hx⟩ := hx
    rw [mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    rw [mem_Ico] at hc
    have hpQ := (mem_Icc.1 (mem_filter.1 hp).1)
    rw [mem_farey]
    refine ⟨hpQ.1, hpQ.2, hc.2, ?_⟩
    show Nat.Coprime c p
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (hprime p hp)]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have h3 : ∑ x ∈ T, f x ≤ ∑ x ∈ farey Q, f x :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  rw [h1, h2]
  exact h3.trans (farey_large_sieve hQ a M N)

/-- **Sifted set bound from the prime modulus large sieve.** -/
private theorem sifted_card_bound {Q : ℕ} (hQ : 1 ≤ Q) (M : ℤ) (N : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Ioc M (M + N)) (ω : ℕ → ℕ) (hω : ∀ p ∈ primesUpTo Q, ω p < p)
    (hres : ∀ p ∈ primesUpTo Q,
      ((range p).filter (fun b : ℕ => ∃ n ∈ A, n % (p : ℤ) = (b : ℤ))).card ≤ p - ω p) :
    (A.card : ℝ) * ∑ p ∈ primesUpTo Q, ((ω p : ℝ) / (p - ω p)) ≤ N + 2 * (Q : ℝ) ^ 2 := by
  set I := Ioc M (M + N)
  set a : ℤ → ℂ := fun n => if n ∈ A then 1 else 0 with ha
  have hprime : ∀ p ∈ primesUpTo Q, p.Prime := fun p hp => (mem_filter.1 hp).2
  have hnorm : ∀ n, ‖a n‖ ^ 2 = if n ∈ A then 1 else 0 := by
    intro n; simp only [ha]; split_ifs <;> simp
  have hsumsq : ∑ n ∈ I, ‖a n‖ ^ 2 = A.card := by
    simp_rw [hnorm]
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, filter_mem_eq_inter,
      inter_eq_right.2 hA]
  -- residue sums are counts
  have hres_eq : ∀ (p : ℕ) (b : ℕ),
      resSum I a p b = (((A.filter (fun n => n % (p : ℤ) = b)).card : ℕ) : ℂ) := by
    intro p b
    unfold resSum
    simp only [ha]
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, filter_filter]
    congr 2
    ext n
    simp only [mem_filter]
    constructor
    · rintro ⟨_, h1, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨hA h2, h1, h2⟩
  have htot : ∑ n ∈ I, a n = (A.card : ℂ) := by
    simp only [ha]
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, filter_mem_eq_inter,
      inter_eq_right.2 hA]
  set Acard : ℝ := (A.card : ℝ)
  -- Cauchy-Schwarz on each prime
  have hcs : ∀ p ∈ primesUpTo Q, Acard ^ 2 * ((ω p : ℝ) / (p - ω p)) ≤
      (p : ℝ) * ∑ b ∈ range p, ‖resSum I a p b‖ ^ 2 - ‖∑ n ∈ I, a n‖ ^ 2 := by
    intro p hp
    have hpp := (hprime p hp).pos
    have hωp := hω p hp
    set R := (range p).filter (fun b : ℕ => ∃ n ∈ A, n % (p : ℤ) = (b : ℤ)) with hR
    set z : ℕ → ℝ := fun b => ((A.filter (fun n => n % (p : ℤ) = b)).card : ℝ) with hz
    have hnormz : ∀ b, ‖resSum I a p b‖ ^ 2 = z b ^ 2 := by
      intro b; rw [hres_eq, Complex.norm_natCast]
    simp_rw [hnormz]
    rw [htot, Complex.norm_natCast]
    -- `|A| = ∑_{b ∈ R} z b`
    have hAsum : Acard = ∑ b ∈ R, z b := by
      have hfib : A.card = ∑ b ∈ range p, (A.filter (fun n => n % (p : ℤ) = b)).card := by
        rw [card_eq_sum_card_fiberwise (f := fun n => (n % (p : ℤ)).toNat)]
        · apply sum_congr rfl; intro b _
          congr 1; ext n; simp only [mem_filter]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h1, by
              have h0 : 0 ≤ n % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hpp.ne')
              omega⟩
          · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]; simp⟩
        · intro n _
          simp only [coe_range, Set.mem_Iio]
          have h0 : 0 ≤ n % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hpp.ne')
          have h1 : n % (p : ℤ) < p := Int.emod_lt_of_pos _ (by exact_mod_cast hpp)
          omega
      have hzero : ∀ b ∈ range p, b ∉ R → z b = 0 := by
        intro b hb hbR
        simp only [hz, Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
        intro n hn hnb
        exact hbR (mem_filter.2 ⟨hb, n, hn, hnb⟩)
      rw [show Acard = ((A.card : ℕ) : ℝ) from rfl, hfib, Nat.cast_sum]
      rw [← sum_subset (filter_subset _ _) hzero]
    have hRcard : (R.card : ℝ) ≤ p - ω p := by
      have := hres p hp
      have : ((R.card : ℕ) : ℝ) ≤ ((p - ω p : ℕ) : ℝ) := by exact_mod_cast this
      rwa [Nat.cast_sub hωp.le] at this
    have hpω : (0 : ℝ) < p - ω p := by
      have : (ω p : ℝ) < p := by exact_mod_cast hωp
      linarith
    have hcs1 : Acard ^ 2 ≤ (p - ω p) * ∑ b ∈ range p, z b ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := R) (f := z)
      rw [← hAsum] at this
      calc Acard ^ 2 ≤ R.card * ∑ b ∈ R, z b ^ 2 := this
        _ ≤ (p - ω p) * ∑ b ∈ R, z b ^ 2 :=
            mul_le_mul_of_nonneg_right hRcard (sum_nonneg (fun _ _ => by positivity))
        _ ≤ (p - ω p) * ∑ b ∈ range p, z b ^ 2 :=
            mul_le_mul_of_nonneg_left
              (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
                (fun _ _ _ => by positivity)) hpω.le
    have hgoal : Acard ^ 2 * ((ω p : ℝ) / (p - ω p)) =
        Acard ^ 2 * (p / (p - ω p)) - Acard ^ 2 := by
      field_simp; ring
    rw [hgoal]
    have : Acard ^ 2 * (p / (p - ω p)) ≤ p * ∑ b ∈ range p, z b ^ 2 := by
      rw [mul_div_assoc', div_le_iff₀ hpω]
      have hp0 : (0 : ℝ) ≤ p := by positivity
      nlinarith
    linarith
  have hmain := prime_large_sieve hQ a M N
  rw [hsumsq] at hmain
  have hsum : Acard ^ 2 * ∑ p ∈ primesUpTo Q, ((ω p : ℝ) / (p - ω p)) ≤
      (N + 2 * (Q : ℝ) ^ 2) * Acard := by
    rw [mul_sum]
    exact (sum_le_sum hcs).trans hmain
  have hA0 : 0 ≤ Acard := Nat.cast_nonneg _
  rcases eq_or_lt_of_le hA0 with h | h
  · rw [← h, zero_mul]; positivity
  · have : Acard * (Acard * ∑ p ∈ primesUpTo Q, ((ω p : ℝ) / (p - ω p))) ≤
        Acard * (N + 2 * (Q : ℝ) ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this h


end

/-! ### copied from PNTPort/LargeSieve/Montgomery.lean -/
section

/-!
# Montgomery's sieve over squarefree moduli

Lab proof, unit U-5551, CLOUD 20261019T1321Z-cloud25. AI wrote this file. Known mathematics,
Montgomery 1968, in the form of Montgomery-Vaughan 1973 with the lab's weak constant `N + 2Q²`.
No cited input.

* `S I a x = ∑_{n ∈ I} a n e(nx)` and `Pr I a q = ∑_{c < q, (c, q) = 1} ‖S I a (c/q)‖²`.
* `Pr_prime_ge`: if `a` vanishes on the residue classes `Bad p` modulo a prime `p`, with
  `ω = |Bad p| < p`, then `Pr I a p ≥ ω/(p - ω) ‖S I a 0‖²`.
* `Pr_mul`: for coprime `q₁, q₂`, `Pr I a (q₁q₂) = ∑_{c ∈ U q₁} Pr I (a · e(·c/q₁)) q₂`, by the
  Chinese remainder theorem.
* `Pr_sqf_ge`: for squarefree `q` whose primes all carry the hypothesis,
  `Pr I a q ≥ h(q) ‖S I a 0‖²`, `h(q) = ∏_{p ∣ q} ω(p)/(p - ω(p))`.
* `montgomery_sieve`: if `A ⊆ (M, M + N]` avoids `Bad p` modulo every prime `p ≤ Q`, then
  `|A| ∑_{q ≤ Q squarefree} h(q) ≤ N + 2Q²`.
-/


open Complex Finset Real

/-- The exponential sum `S(x) = ∑_{n ∈ I} a n e(nx)`. -/
private noncomputable def S (I : Finset ℤ) (a : ℤ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ I, a n * e (n * x)

/-- The reduced residues modulo `q`, in the order `Nat.totient` uses. -/
private def U (q : ℕ) : Finset ℕ := (range q).filter (Nat.Coprime q)

private lemma card_U (q : ℕ) : (U q).card = q.totient := rfl

/-- The sum over primitive fractions `c/q`. -/
private noncomputable def Pr (I : Finset ℤ) (a : ℤ → ℂ) (q : ℕ) : ℝ :=
  ∑ c ∈ U q, ‖S I a ((c : ℝ) / q)‖ ^ 2

private lemma S_add_int (I : Finset ℤ) (a : ℤ → ℂ) (x : ℝ) (k : ℤ) : S I a (x + k) = S I a x := by
  unfold S
  refine sum_congr rfl fun n _ => ?_
  rw [mul_add, e_add, show ((n : ℝ) * (k : ℝ)) = ((n * k : ℤ) : ℝ) by push_cast; ring, e_int,
    mul_one]

private lemma S_twist (I : Finset ℤ) (a : ℤ → ℂ) (x y : ℝ) :
    S I (fun n => a n * e (n * x)) y = S I a (x + y) := by
  unfold S
  refine sum_congr rfl fun n _ => ?_
  rw [mul_assoc, ← e_add, mul_add]

private lemma resSum_fiber (I : Finset ℤ) (a : ℤ → ℂ) {p : ℕ} (hp : 0 < p) (b : ℕ) :
    resSum I a p b = ∑ n ∈ I.filter (fun n : ℤ => (n % (p : ℤ)).toNat = b), a n := by
  unfold resSum
  congr 1
  ext n
  simp only [mem_filter]
  have h0 : 0 ≤ n % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]; simp⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

private lemma S_zero_eq_sum_res (I : Finset ℤ) (a : ℤ → ℂ) {p : ℕ} (hp : 0 < p) :
    S I a 0 = ∑ b ∈ range p, resSum I a p b := by
  simp_rw [resSum_fiber I a hp]
  unfold S
  simp only [mul_zero, e_zero, mul_one]
  refine (sum_fiberwise_of_maps_to (g := fun n : ℤ => (n % (p : ℤ)).toNat) ?_ _).symm
  intro n _
  rw [mem_range]
  have h0 : 0 ≤ n % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
  have h1 : n % (p : ℤ) < p := Int.emod_lt_of_pos _ (by exact_mod_cast hp)
  omega

/-- `a` vanishes on the classes `B` modulo `p`. -/
private def Avoids (I : Finset ℤ) (a : ℤ → ℂ) (p : ℕ) (B : Finset ℕ) : Prop :=
  ∀ n ∈ I, (n % (p : ℤ)).toNat ∈ B → a n = 0

private lemma avoids_twist {I : Finset ℤ} {a : ℤ → ℂ} {p : ℕ} {B : Finset ℕ} (h : Avoids I a p B)
    (x : ℝ) : Avoids I (fun n => a n * e (n * x)) p B := by
  intro n hn hb
  show a n * _ = 0
  rw [h n hn hb, zero_mul]

private lemma U_prime {p : ℕ} (hp : p.Prime) : U p = (range p).erase 0 := by
  ext c
  simp only [U, mem_filter, mem_range, mem_erase]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    rintro rfl
    rw [Nat.coprime_zero_right] at h2
    exact hp.one_lt.ne' h2
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    exact h1 (Nat.eq_zero_of_dvd_of_lt hd h2)

/-- The prime case of Montgomery's inequality. -/
private theorem Pr_prime_ge (I : Finset ℤ) (a : ℤ → ℂ) {p : ℕ} (hp : p.Prime) {B : Finset ℕ}
    (hB : B ⊆ range p) (hBp : B.card < p) (ha : Avoids I a p B) :
    (B.card : ℝ) / (p - B.card) * ‖S I a 0‖ ^ 2 ≤ Pr I a p := by
  have hp0 := hp.pos
  set z : ℕ → ℂ := fun b => resSum I a p b with hz
  have hzero : ∀ b ∈ B, z b = 0 := by
    intro b hb
    simp only [hz]
    rw [resSum_fiber I a hp0]
    refine sum_eq_zero fun n hn => ?_
    rw [mem_filter] at hn
    exact ha n hn.1 (by rw [hn.2]; exact hb)
  -- the full sum by Parseval
  have hpars := parseval_mod I a hp0
  have hfull : ∑ c ∈ range p, ‖S I a ((c : ℝ) / p)‖ ^ 2 = p * ∑ b ∈ range p, ‖z b‖ ^ 2 := by
    rw [← hpars]
    refine sum_congr rfl fun c _ => ?_
    unfold S
    congr 2
    refine sum_congr rfl fun n _ => ?_
    rw [mul_div_assoc]
  have hsplit : ∑ c ∈ range p, ‖S I a ((c : ℝ) / p)‖ ^ 2 = Pr I a p + ‖S I a 0‖ ^ 2 := by
    unfold Pr
    rw [U_prime hp, ← add_sum_erase _ _ (mem_range.2 hp0)]
    simp only [Nat.cast_zero, zero_div]
    ring
  -- Cauchy-Schwarz over the classes outside `B`
  set R := range p \ B with hR
  have hS0 : S I a 0 = ∑ b ∈ R, z b := by
    rw [S_zero_eq_sum_res I a hp0, hR, sum_sdiff_eq_sub hB]
    rw [sum_eq_zero hzero, sub_zero]
  have hRcard : (R.card : ℝ) = p - B.card := by
    rw [hR, card_sdiff_of_subset hB, card_range, Nat.cast_sub hBp.le]
  have hcs : ‖S I a 0‖ ^ 2 ≤ (p - B.card) * ∑ b ∈ range p, ‖z b‖ ^ 2 := by
    rw [hS0]
    have h1 : ‖∑ b ∈ R, z b‖ ≤ ∑ b ∈ R, ‖z b‖ := norm_sum_le _ _
    have h2 := sq_sum_le_card_mul_sum_sq (s := R) (f := fun b => ‖z b‖)
    have h3 : ∑ b ∈ R, ‖z b‖ ^ 2 ≤ ∑ b ∈ range p, ‖z b‖ ^ 2 :=
      sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => by positivity)
    rw [← hRcard]
    calc ‖∑ b ∈ R, z b‖ ^ 2 ≤ (∑ b ∈ R, ‖z b‖) ^ 2 := by gcongr
      _ ≤ R.card * ∑ b ∈ R, ‖z b‖ ^ 2 := h2
      _ ≤ R.card * ∑ b ∈ range p, ‖z b‖ ^ 2 := by gcongr
  have hpω : (0 : ℝ) < p - B.card := by
    have : (B.card : ℝ) < p := by exact_mod_cast hBp
    linarith
  -- assemble
  have hT : ‖S I a 0‖ ^ 2 / (p - B.card) ≤ ∑ b ∈ range p, ‖z b‖ ^ 2 := by
    rw [div_le_iff₀ hpω]; linarith
  have hP : Pr I a p = p * ∑ b ∈ range p, ‖z b‖ ^ 2 - ‖S I a 0‖ ^ 2 := by linarith
  rw [hP]
  have : (B.card : ℝ) / (p - B.card) * ‖S I a 0‖ ^ 2 =
      p * (‖S I a 0‖ ^ 2 / (p - B.card)) - ‖S I a 0‖ ^ 2 := by
    field_simp; ring
  rw [this]
  have hp' : (0 : ℝ) ≤ p := by positivity
  nlinarith

/-- The Chinese remainder map on reduced residues. -/
private def crt (q₁ q₂ : ℕ) (c : ℕ × ℕ) : ℕ := (c.1 * q₂ + c.2 * q₁) % (q₁ * q₂)

private lemma coprime_of_mod {m x y : ℕ} (h : x % m = y % m) (hy : Nat.Coprime m y) : Nat.Coprime m x := by
  unfold Nat.Coprime at *
  rw [Nat.gcd_rec m x, h, ← Nat.gcd_rec, hy]

private lemma crt_mem {q₁ q₂ : ℕ} (h : Nat.Coprime q₁ q₂) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) {c : ℕ × ℕ}
    (hc : c ∈ U q₁ ×ˢ U q₂) : crt q₁ q₂ c ∈ U (q₁ * q₂) := by
  simp only [U, mem_product, mem_filter, mem_range] at hc
  simp only [U, mem_filter, mem_range, crt]
  refine ⟨Nat.mod_lt _ (Nat.mul_pos hq₁ hq₂), Nat.coprime_mul_iff_left.2 ⟨?_, ?_⟩⟩
  · apply coprime_of_mod (y := c.1 * q₂)
    · rw [Nat.mod_mod_of_dvd _ (dvd_mul_right q₁ q₂), Nat.add_mul_mod_self_right]
    · exact Nat.coprime_mul_iff_right.2 ⟨hc.1.2, h⟩
  · apply coprime_of_mod (y := c.2 * q₁)
    · rw [Nat.mod_mod_of_dvd _ (dvd_mul_left q₂ q₁), add_comm, Nat.add_mul_mod_self_right]
    · exact Nat.coprime_mul_iff_right.2 ⟨hc.2.2, h.symm⟩

private lemma crt_inj {q₁ q₂ : ℕ} (h : Nat.Coprime q₁ q₂) {c d : ℕ × ℕ}
    (hc : c ∈ U q₁ ×ˢ U q₂) (hd : d ∈ U q₁ ×ˢ U q₂) (he : crt q₁ q₂ c = crt q₁ q₂ d) :
    c = d := by
  simp only [U, mem_product, mem_filter, mem_range] at hc hd
  have hmod : c.1 * q₂ + c.2 * q₁ ≡ d.1 * q₂ + d.2 * q₁ [MOD q₁ * q₂] := he
  have h1 : c.1 * q₂ ≡ d.1 * q₂ [MOD q₁] := by
    have := Nat.ModEq.of_mul_right q₂ hmod
    unfold Nat.ModEq at this ⊢
    rwa [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at this
  have h2 : c.2 * q₁ ≡ d.2 * q₁ [MOD q₂] := by
    have := Nat.ModEq.of_mul_left q₁ hmod
    unfold Nat.ModEq at this ⊢
    rwa [add_comm, Nat.add_mul_mod_self_right, add_comm, Nat.add_mul_mod_self_right] at this
  have e1 := Nat.ModEq.cancel_right_of_coprime h h1
  have e2 := Nat.ModEq.cancel_right_of_coprime h.symm h2
  unfold Nat.ModEq at e1 e2
  rw [Nat.mod_eq_of_lt hc.1.1, Nat.mod_eq_of_lt hd.1.1] at e1
  rw [Nat.mod_eq_of_lt hc.2.1, Nat.mod_eq_of_lt hd.2.1] at e2
  exact Prod.ext e1 e2

private lemma crt_image {q₁ q₂ : ℕ} (h : Nat.Coprime q₁ q₂) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) :
    (U q₁ ×ˢ U q₂).image (crt q₁ q₂) = U (q₁ * q₂) := by
  apply eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
    exact crt_mem h hq₁ hq₂ hc
  · rw [card_image_of_injOn (fun c hc d hd he => crt_inj h hc hd he), card_product, card_U,
      card_U, card_U, Nat.totient_mul h]

private lemma S_crt (I : Finset ℤ) (a : ℤ → ℂ) {q₁ q₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (c : ℕ × ℕ) :
    S I a ((crt q₁ q₂ c : ℕ) / ((q₁ * q₂ : ℕ) : ℝ)) =
      S I a ((c.1 : ℝ) / q₁ + (c.2 : ℝ) / q₂) := by
  set x := c.1 * q₂ + c.2 * q₁
  set m := q₁ * q₂
  have hm : (0 : ℝ) < m := by positivity
  have hdiv : x = m * (x / m) + x % m := (Nat.div_add_mod x m).symm
  have hx : (x : ℝ) = m * ((x / m : ℕ) : ℝ) + ((x % m : ℕ) : ℝ) := by exact_mod_cast hdiv
  have hq1 : (q₁ : ℝ) ≠ 0 := by positivity
  have hq2 : (q₂ : ℝ) ≠ 0 := by positivity
  have hxdef : (x : ℝ) = c.1 * q₂ + c.2 * q₁ := by simp [x]
  have hmdef : (m : ℝ) = q₁ * q₂ := by simp [m]
  have k1 : (c.1 : ℝ) / q₁ + (c.2 : ℝ) / q₂ = (x : ℝ) / m := by
    rw [hxdef, hmdef]; field_simp
  have k2 : (x : ℝ) / m = ((x % m : ℕ) : ℝ) / (m : ℝ) + (((x / m : ℕ) : ℤ) : ℝ) := by
    rw [hx, Int.cast_natCast]; field_simp; ring
  rw [k1, k2, S_add_int]
  rfl

/-- Multiplicativity of the primitive sums, by the Chinese remainder theorem. -/
private theorem Pr_mul (I : Finset ℤ) (a : ℤ → ℂ) {q₁ q₂ : ℕ} (h : Nat.Coprime q₁ q₂) (hq₁ : 0 < q₁)
    (hq₂ : 0 < q₂) :
    Pr I a (q₁ * q₂) = ∑ c ∈ U q₁, Pr I (fun n => a n * e (n * ((c : ℝ) / q₁))) q₂ := by
  unfold Pr
  simp_rw [S_twist]
  rw [← sum_product (f := fun c : ℕ × ℕ => ‖S I a ((c.1 : ℝ) / q₁ + (c.2 : ℝ) / q₂)‖ ^ 2),
    ← crt_image h hq₁ hq₂, sum_image (fun c hc d hd he => crt_inj h hc hd he)]
  refine sum_congr rfl fun c _ => ?_
  rw [← S_crt I a hq₁ hq₂ c]

/-- The weight `h(q) = ∏_{p ∣ q} ω(p)/(p - ω(p))`. -/
private noncomputable def hW (B : ℕ → Finset ℕ) (q : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors, ((B p).card : ℝ) / (p - (B p).card)

private lemma Pr_one (I : Finset ℤ) (a : ℤ → ℂ) : Pr I a 1 = ‖S I a 0‖ ^ 2 := by
  unfold Pr U
  rw [show (range 1).filter (Nat.Coprime 1) = {0} by decide, sum_singleton]
  simp

/-- Montgomery's inequality for a squarefree modulus. -/
private theorem Pr_sqf_ge (I : Finset ℤ) (a : ℤ → ℂ) (B : ℕ → Finset ℕ)
    (hB : ∀ p, p.Prime → B p ⊆ range p ∧ (B p).card < p) :
    ∀ q, Squarefree q → (∀ p ∈ q.primeFactors, Avoids I a p (B p)) →
      hW B q * ‖S I a 0‖ ^ 2 ≤ Pr I a q := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro hq hav
  rcases Nat.lt_or_ge q 2 with hlt | hge
  · interval_cases q
    · exact absurd hq not_squarefree_zero
    · simp [hW, Pr_one]
  · obtain ⟨p, hpdef⟩ : ∃ p, p = q.minFac := ⟨_, rfl⟩
    have hp : p.Prime := hpdef ▸ Nat.minFac_prime (by omega)
    have hpq : p ∣ q := hpdef ▸ Nat.minFac_dvd q
    obtain ⟨q₁, hq₁def⟩ : ∃ q₁, q₁ = q / p := ⟨_, rfl⟩
    have hq_eq : q = q₁ * p := by rw [hq₁def]; exact (Nat.div_mul_cancel hpq).symm
    have hq₁pos : 0 < q₁ := hq₁def ▸ Nat.div_pos (Nat.le_of_dvd (by omega) hpq) hp.pos
    have hcop : Nat.Coprime q₁ p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro hd
      have : p * p ∣ q := by rw [hq_eq]; exact Nat.mul_dvd_mul_right hd p
      exact hp.one_lt.ne' (Nat.isUnit_iff.1 (hq p this))
    have hq₁lt : q₁ < q := hq₁def ▸ Nat.div_lt_self (by omega) hp.one_lt
    have hq₁sqf : Squarefree q₁ := hq.squarefree_of_dvd (hq₁def ▸ Nat.div_dvd_of_dvd hpq)
    have hpf : q.primeFactors = insert p q₁.primeFactors := by
      rw [hq_eq, Nat.primeFactors_mul hq₁pos.ne' hp.ne_zero, hp.primeFactors, union_comm]; rfl
    have hpnot : p ∉ q₁.primeFactors := by
      intro hm
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop.symm (Nat.dvd_of_mem_primeFactors hm)
    have hav₁ : ∀ r ∈ q₁.primeFactors, Avoids I a r (B r) := fun r hr =>
      hav r (by rw [hpf]; exact mem_insert_of_mem hr)
    have havp : Avoids I a p (B p) := hav p (by rw [hpf]; exact mem_insert_self _ _)
    have hW_eq : hW B q = ((B p).card : ℝ) / (p - (B p).card) * hW B q₁ := by
      unfold hW; rw [hpf, prod_insert hpnot]
    have hBp := hB p hp
    have hhp : (0 : ℝ) ≤ ((B p).card : ℝ) / (p - (B p).card) := by
      have : ((B p).card : ℝ) < p := by exact_mod_cast hBp.2
      exact div_nonneg (Nat.cast_nonneg _) (by linarith)
    rw [hW_eq]
    clear hq₁def hpdef hpf
    subst hq_eq
    rw [Pr_mul I a hcop hq₁pos hp.pos]
    have step : ∀ c ∈ U q₁, ((B p).card : ℝ) / (p - (B p).card) * ‖S I a ((c : ℝ) / q₁)‖ ^ 2 ≤
        Pr I (fun n => a n * e (n * ((c : ℝ) / q₁))) p := by
      intro c _
      have := Pr_prime_ge I (fun n => a n * e (n * ((c : ℝ) / q₁))) hp hBp.1 hBp.2
        (avoids_twist havp _)
      rwa [S_twist, add_zero] at this
    calc ((B p).card : ℝ) / (p - (B p).card) * hW B q₁ * ‖S I a 0‖ ^ 2
        = ((B p).card : ℝ) / (p - (B p).card) * (hW B q₁ * ‖S I a 0‖ ^ 2) := by ring
      _ ≤ ((B p).card : ℝ) / (p - (B p).card) * Pr I a q₁ := by
          exact mul_le_mul_of_nonneg_left (ih q₁ hq₁lt hq₁sqf hav₁) hhp
      _ = ∑ c ∈ U q₁, ((B p).card : ℝ) / (p - (B p).card) * ‖S I a ((c : ℝ) / q₁)‖ ^ 2 := by
          unfold Pr; rw [mul_sum]
      _ ≤ _ := sum_le_sum step

/-- The Farey sum regrouped by denominator. -/
private lemma farey_sum_eq (Q : ℕ) (F : ℕ × ℕ → ℝ) :
    ∑ x ∈ farey Q, F x = ∑ q ∈ Icc 1 Q, ∑ c ∈ U q, F (q, c) := by
  unfold farey
  rw [sum_filter, sum_product]
  refine sum_congr rfl fun q hq => ?_
  rw [mem_Icc] at hq
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext c
  simp only [mem_filter, mem_range, U]
  constructor
  · rintro ⟨_, h1, h2⟩; exact ⟨h1, Nat.coprime_comm.1 h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, Nat.coprime_comm.1 h2⟩

/-- **Montgomery's sieve.** If `A ⊆ (M, M + N]` avoids the classes `B p` modulo every prime
`p ≤ Q`, with `|B p| < p`, then `|A| ∑_{q ≤ Q squarefree} h(q) ≤ N + 2Q²`. -/
private theorem montgomery_sieve {Q : ℕ} (hQ : 1 ≤ Q) (M : ℤ) (N : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Ioc M (M + N)) (B : ℕ → Finset ℕ)
    (hB : ∀ p, p.Prime → B p ⊆ range p ∧ (B p).card < p)
    (hAB : ∀ p, p.Prime → p ≤ Q → ∀ n ∈ A, (n % (p : ℤ)).toNat ∉ B p) :
    (A.card : ℝ) * ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q ≤ N + 2 * (Q : ℝ) ^ 2 := by
  set I := Ioc M (M + N)
  set a : ℤ → ℂ := fun n => if n ∈ A then 1 else 0 with ha
  have hS0 : S I a 0 = A.card := by
    unfold S
    simp only [ha, mul_zero, e_zero, mul_one]
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, filter_mem_eq_inter,
      inter_eq_right.2 hA]
  have hsq : ∑ n ∈ I, ‖a n‖ ^ 2 = A.card := by
    have : ∀ n, ‖a n‖ ^ 2 = if n ∈ A then 1 else 0 := by
      intro n; simp only [ha]; split_ifs <;> simp
    simp_rw [this]
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, filter_mem_eq_inter,
      inter_eq_right.2 hA]
  have hls := farey_large_sieve hQ a M N
  rw [hsq] at hls
  have hfs : ∑ p ∈ farey Q, ‖∑ n ∈ I, a n * e (n * fareyPt p)‖ ^ 2 =
      ∑ q ∈ Icc 1 Q, Pr I a q := by
    rw [farey_sum_eq Q (fun p => ‖∑ n ∈ I, a n * e (n * fareyPt p)‖ ^ 2)]
    rfl
  rw [hfs] at hls
  have hlow : ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q * (A.card : ℝ) ^ 2 ≤
      ∑ q ∈ Icc 1 Q, Pr I a q := by
    calc ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q * (A.card : ℝ) ^ 2
        ≤ ∑ q ∈ (Icc 1 Q).filter Squarefree, Pr I a q := by
          refine sum_le_sum fun q hq => ?_
          rw [mem_filter, mem_Icc] at hq
          have := Pr_sqf_ge I a B hB q hq.2 (fun p hp => by
            intro n hn hb
            have hpQ : p ≤ Q := (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)).trans
              hq.1.2
            simp only [ha, ite_eq_right_iff, one_ne_zero, imp_false]
            intro hnA
            exact hAB p (Nat.prime_of_mem_primeFactors hp) hpQ n hnA hb)
          rwa [hS0, Complex.norm_natCast] at this
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun q _ _ => by unfold Pr; positivity)
  rw [← sum_mul] at hlow
  rcases Nat.eq_zero_or_pos A.card with h0 | hpos
  · rw [h0]; simp; positivity
  · have hpos' : (0 : ℝ) < A.card := by exact_mod_cast hpos
    have := hlow.trans hls
    rw [show (A.card : ℝ) ^ 2 = A.card * A.card by ring, ← mul_assoc] at this
    have := le_of_mul_le_mul_right this hpos'
    linarith


end

/-! ### copied from PNTPort/LargeSieve/MontgomeryBT.lean -/
section

/-!
# Brun-Titchmarsh from Montgomery's sieve, explicit

Lab proof, unit U-5551, CLOUD 20261019T1321Z-cloud25. AI wrote this file. Known mathematics,
Montgomery 1968; the sharp form `2y/log y` is Montgomery-Vaughan 1973, here with the lab's weak
large sieve constant `N + 2Q²`. No cited input.

* `sum_inv_pf_eq_le`: `∑_{n ≤ Q, primeFactors n = P} 1/n ≤ ∏_{p ∈ P} 1/(p - 1)`.
* `log_le_sum_sqf`: `log(Q + 1) ≤ ∑_{q ≤ Q squarefree} ∏_{p ∣ q} 1/(p - 1) = ∑_{q ≤ Q} μ²(q)/φ(q)`.
* `brun_titchmarsh_montgomery`: for every `x, y` and `Q ≥ 1`,
  `π(x + y) - π(x) ≤ Q + (y + 2Q²)/log(Q + 1)`. With `Q` near `√y / log y` this is
  `π(x + y) - π(x) ≤ (2 + o(1)) y / log y`, with an error of order `y log log y / log² y`,
  no `y (log y)³` term.
-/


open Finset Real

/-- `∑_{y ∈ f(s)} g y ≤ ∑_{x ∈ s} g (f x)` for `g ≥ 0`. -/
private lemma sum_image_le_of_nonneg' {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β)
    (g : β → ℝ) (hg : ∀ y, 0 ≤ g y) : ∑ y ∈ s.image f, g y ≤ ∑ x ∈ s, g (f x) := by
  rw [Finset.sum_comp g f]
  refine sum_le_sum fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
  have h1 : 1 ≤ (s.filter (fun a => f a = f x)).card :=
    card_pos.2 ⟨x, mem_filter.2 ⟨hx, rfl⟩⟩
  rw [nsmul_eq_mul]
  have : (1 : ℝ) ≤ (s.filter (fun a => f a = f x)).card := by exact_mod_cast h1
  nlinarith [hg (f x)]

private lemma geom_inv_le {p : ℕ} (hp : p.Prime) (Q : ℕ) :
    ∑ k ∈ Icc 1 Q, (1 / (p : ℝ)) ^ k ≤ 1 / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have h1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have := geom_sum_Ico_le_of_lt_one (m := 1) (n := Q + 1) h0 h1
  rw [show Icc 1 Q = Ico 1 (Q + 1) by ext; simp]
  refine this.trans (le_of_eq ?_)
  field_simp

/-- The fibre of `n ↦ primeFactors n` over a finite set of primes. -/
private theorem sum_inv_pf_eq_le (Q : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ n ∈ (Icc 1 Q).filter (fun n => n.primeFactors = P), (1 / (n : ℝ)) ≤
      ∏ p ∈ P, 1 / ((p : ℝ) - 1) := by
  induction P using Finset.induction_on with
  | empty =>
    rw [prod_empty]
    have : (Icc 1 Q).filter (fun n => n.primeFactors = ∅) ⊆ {1} := by
      intro n hn
      rw [mem_filter, Nat.primeFactors_eq_empty, mem_Icc] at hn
      rw [mem_singleton]; omega
    refine (sum_le_sum_of_subset_of_nonneg this (fun _ _ _ => by positivity)).trans ?_
    simp
  | insert p P' hpP' ih =>
    have hp : p.Prime := hP p (mem_insert_self _ _)
    have hP' : ∀ r ∈ P', r.Prime := fun r hr => hP r (mem_insert_of_mem hr)
    set T' := (Icc 1 Q).filter (fun n => n.primeFactors = P')
    have hsub : (Icc 1 Q).filter (fun n => n.primeFactors = insert p P') ⊆
        (Icc 1 Q ×ˢ T').image (fun km : ℕ × ℕ => p ^ km.1 * km.2) := by
      intro n hn
      rw [mem_filter, mem_Icc] at hn
      obtain ⟨⟨hn1, hnQ⟩, hpf⟩ := hn
      have hn0 : n ≠ 0 := by omega
      have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors (by rw [hpf]; exact mem_insert_self _ _)
      set k := n.factorization p
      have hk1 : 1 ≤ k := hp.factorization_pos_of_dvd hn0 hpn
      have hpk : p ^ k ∣ n := Nat.ordProj_dvd n p
      have hkQ : k ≤ Q := by
        have := Nat.lt_pow_self hp.one_lt (n := k)
        have := Nat.le_of_dvd (by omega) hpk
        omega
      set m := n / p ^ k
      have hm0 : 0 < m := Nat.ordCompl_pos p hn0
      have hmQ : m ≤ Q := (Nat.div_le_self n _).trans hnQ
      have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp hn0
      have hmn : n = p ^ k * m := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
      have hpfm : m.primeFactors = P' := by
        ext r
        constructor
        · intro hr
          have hrn : r ∈ n.primeFactors :=
            Nat.primeFactors_mono (Nat.ordCompl_dvd n p) hn0 hr
          rw [hpf, mem_insert] at hrn
          rcases hrn with rfl | h
          · exact absurd (Nat.dvd_of_mem_primeFactors hr)
              ((Nat.Prime.coprime_iff_not_dvd hp).1 hcop)
          · exact h
        · intro hr
          have hrn : r ∈ n.primeFactors := by rw [hpf]; exact mem_insert_of_mem hr
          have hrp : r ≠ p := fun h => hpP' (h ▸ hr)
          have hrprime := hP' r hr
          have hcr : Nat.Coprime r (p ^ k) :=
            Nat.Coprime.pow_right k ((Nat.coprime_primes hrprime hp).2 hrp)
          have hrd : r ∣ p ^ k * m := hmn ▸ Nat.dvd_of_mem_primeFactors hrn
          exact Nat.mem_primeFactors.2 ⟨hrprime, hcr.dvd_of_dvd_mul_left hrd, hm0.ne'⟩
      refine mem_image.2 ⟨(k, m), ?_, hmn.symm⟩
      rw [mem_product, mem_Icc]
      exact ⟨⟨hk1, hkQ⟩, mem_filter.2 ⟨mem_Icc.2 ⟨hm0, hmQ⟩, hpfm⟩⟩
    calc ∑ n ∈ (Icc 1 Q).filter (fun n => n.primeFactors = insert p P'), (1 / (n : ℝ))
        ≤ ∑ n ∈ (Icc 1 Q ×ˢ T').image (fun km : ℕ × ℕ => p ^ km.1 * km.2), (1 / (n : ℝ)) :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ ∑ km ∈ Icc 1 Q ×ˢ T', (1 / ((p ^ km.1 * km.2 : ℕ) : ℝ)) :=
          sum_image_le_of_nonneg' _ _ (fun n : ℕ => 1 / (n : ℝ)) (fun _ => by positivity)
      _ = (∑ k ∈ Icc 1 Q, (1 / (p : ℝ)) ^ k) * ∑ m ∈ T', (1 / (m : ℝ)) := by
          rw [sum_mul_sum, sum_product]
          refine sum_congr rfl fun k _ => sum_congr rfl fun m _ => ?_
          push_cast
          rw [one_div_pow, one_div_mul_one_div]
      _ ≤ 1 / ((p : ℝ) - 1) * ∏ r ∈ P', 1 / ((r : ℝ) - 1) := by
          apply mul_le_mul (geom_inv_le hp Q) (ih hP') (sum_nonneg fun _ _ => by positivity)
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
          exact div_nonneg zero_le_one (by linarith)
      _ = ∏ r ∈ insert p P', 1 / ((r : ℝ) - 1) := by rw [prod_insert hpP']

/-- The radical `∏_{p ∣ n} p`. -/
private def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

private lemma rad_pf (n : ℕ) : (rad n).primeFactors = n.primeFactors :=
  Nat.primeFactors_prod (fun _ hp => Nat.prime_of_mem_primeFactors hp)

private lemma rad_sqf (n : ℕ) : Squarefree (rad n) := by
  unfold rad
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    fun p hp => (Nat.prime_of_mem_primeFactors hp).prime.squarefree
  simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq)).mpr hpq

private lemma rad_pos (n : ℕ) : 0 < rad n :=
  prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

/-- `log(Q + 1) ≤ ∑_{q ≤ Q squarefree} ∏_{p ∣ q} 1/(p - 1)`. -/
private theorem log_le_sum_sqf (Q : ℕ) :
    Real.log ((Q : ℝ) + 1) ≤
      ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1) := by
  have hH := log_add_one_le_harmonic Q
  rw [harmonic_eq_sum_Icc] at hH
  push_cast at hH
  refine hH.trans ?_
  rw [← sum_fiberwise_of_maps_to (s := Icc 1 Q) (t := (Icc 1 Q).filter Squarefree) (g := rad)
    (fun n hn => by
      rw [mem_Icc] at hn
      refine mem_filter.2 ⟨mem_Icc.2 ⟨rad_pos n, ?_⟩, rad_sqf n⟩
      exact (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)).trans hn.2)]
  refine sum_le_sum fun q hq => ?_
  rw [mem_filter] at hq
  have hsub : (Icc 1 Q).filter (fun n => rad n = q) ⊆
      (Icc 1 Q).filter (fun n => n.primeFactors = q.primeFactors) := by
    intro n hn
    rw [mem_filter] at hn ⊢
    exact ⟨hn.1, by rw [← rad_pf n, hn.2]⟩
  calc ∑ n ∈ (Icc 1 Q).filter (fun n => rad n = q), ((n : ℝ))⁻¹
      ≤ ∑ n ∈ (Icc 1 Q).filter (fun n => n.primeFactors = q.primeFactors), (1 / (n : ℝ)) := by
        simp_rw [one_div]
        exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ _ := sum_inv_pf_eq_le Q _ (fun p hp => Nat.prime_of_mem_primeFactors hp)

/-- **Brun-Titchmarsh, explicit, from Montgomery's sieve.** For `Q ≥ 1`,
`π(x + y) - π(x) ≤ Q + (y + 2Q²)/log(Q + 1)`. -/
private theorem brun_titchmarsh_montgomery (x y Q : ℕ) (hQ : 1 ≤ Q) :
    ((((Ioc x (x + y)).filter Nat.Prime).card : ℕ) : ℝ) ≤
      Q + (y + 2 * (Q : ℝ) ^ 2) / Real.log ((Q : ℝ) + 1) := by
  set P := (Ioc x (x + y)).filter Nat.Prime
  set Psmall := P.filter (· ≤ Q)
  set Pbig := P.filter (fun r => ¬ r ≤ Q)
  have hsplit : P.card = Psmall.card + Pbig.card := (card_filter_add_card_filter_not _).symm
  have hsmall : (Psmall.card : ℝ) ≤ Q := by
    have : Psmall ⊆ Icc 1 Q := by
      intro r hr
      simp only [Psmall, P, mem_filter, mem_Ioc] at hr
      exact mem_Icc.2 ⟨hr.1.2.one_lt.le, hr.2⟩
    have := card_le_card this
    rw [Nat.card_Icc] at this
    exact_mod_cast (by omega : Psmall.card ≤ Q)
  -- the big primes as integers
  set A : Finset ℤ := Pbig.image (fun r : ℕ => (r : ℤ))
  have hAcard : A.card = Pbig.card := card_image_of_injective _ Nat.cast_injective
  have hA : A ⊆ Ioc (x : ℤ) ((x : ℤ) + (y : ℕ)) := by
    intro n hn
    obtain ⟨r, hr, rfl⟩ := mem_image.1 hn
    simp only [Pbig, P, mem_filter, mem_Ioc] at hr
    rw [mem_Ioc]
    constructor <;> push_cast <;> omega
  set B : ℕ → Finset ℕ := fun _ => {0}
  have hB : ∀ p, p.Prime → B p ⊆ range p ∧ (B p).card < p := by
    intro p hp
    refine ⟨?_, ?_⟩
    · intro b hb
      rw [mem_singleton] at hb
      rw [hb, mem_range]; exact hp.pos
    · rw [card_singleton]; exact hp.one_lt
  have hAB : ∀ p, p.Prime → p ≤ Q → ∀ n ∈ A, (n % (p : ℤ)).toNat ∉ B p := by
    intro p hp hpQ n hn
    obtain ⟨r, hr, rfl⟩ := mem_image.1 hn
    simp only [Pbig, P, mem_filter, mem_Ioc] at hr
    simp only [B, mem_singleton]
    rw [← Int.natCast_mod, Int.toNat_natCast]
    intro h0
    have hdvd : p ∣ r := Nat.dvd_of_mod_eq_zero h0
    have := (Nat.prime_dvd_prime_iff_eq hp hr.1.2).1 hdvd
    omega
  have hmont := montgomery_sieve hQ (x : ℤ) y A hA B hB hAB
  have hW_eq : ∀ q, hW B q = ∏ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1) := by
    intro q
    unfold hW
    refine prod_congr rfl fun _ _ => ?_
    simp [B]
  simp_rw [hW_eq] at hmont
  have hlog := log_le_sum_sqf Q
  have hlogpos : 0 < Real.log ((Q : ℝ) + 1) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have hbig : (Pbig.card : ℝ) ≤ (y + 2 * (Q : ℝ) ^ 2) / Real.log ((Q : ℝ) + 1) := by
    rw [le_div_iff₀ hlogpos, ← hAcard]
    calc (A.card : ℝ) * Real.log ((Q : ℝ) + 1)
        ≤ (A.card : ℝ) * ∑ q ∈ (Icc 1 Q).filter Squarefree,
            ∏ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
      _ ≤ _ := hmont
  rw [hsplit, Nat.cast_add]
  linarith


end

/-! ### copied from PNTPort/LargeSieve/MontgomeryAP.lean -/
section

/-!
# Brun-Titchmarsh in arithmetic progressions from Montgomery's sieve

Lab proof, unit U-5553, CLOUD 20261019T1321Z-cloud25. AI wrote this file. Known mathematics,
Montgomery 1968, with the lab's weak large sieve constant `N + 2Q²`. No cited input.

* `fP q = ∏_{p ∣ q} 1/(p - 1)`, so `fP q = 1/φ(q)` for squarefree `q`.
* `sum_divisors_rad_fP`: `∑_{d ∣ rad k} fP d = k/φ(k)`.
* `sum_sqf_le_coprime`: `∑_{q ≤ Q sqf} fP q ≤ k/φ(k) · ∑_{q ≤ Q sqf, (q,k)=1} fP q`.
* `brun_titchmarsh_ap_montgomery`: for `k, Q ≥ 1` the number of primes `p ≡ r mod k` in
  `(x, x + y]` is at most `Q + (y/k + 2 + 2Q²) · k / (φ(k) log(Q + 1))`.
-/


open Finset Real

/-- `fP q = ∏_{p ∣ q} 1/(p - 1)`. -/
private noncomputable def fP (q : ℕ) : ℝ := ∏ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1)

private lemma fP_nonneg (q : ℕ) : 0 ≤ fP q :=
  prod_nonneg fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    exact div_nonneg zero_le_one (by linarith)

private lemma fP_mul {m n : ℕ} (h : Nat.Coprime m n) : fP (m * n) = fP m * fP n := by
  unfold fP
  rw [Nat.Coprime.primeFactors_mul h, prod_union h.disjoint_primeFactors]

/-- `fP` as a multiplicative arithmetic function. -/
private noncomputable def fPA : ArithmeticFunction ℝ := ⟨fun d => if d = 0 then 0 else fP d, by simp⟩

private lemma fPA_mult : fPA.IsMultiplicative := by
  refine ⟨by simp [fPA, fP], fun {m n} h => ?_⟩
  show (if m * n = 0 then 0 else fP (m * n)) = (if m = 0 then 0 else fP m) * (if n = 0 then 0 else fP n)
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn, fP_mul h]

/-- `∑_{d ∣ rad k} fP d = k/φ(k)`. -/
private theorem sum_divisors_rad_fP {k : ℕ} (hk : 1 ≤ k) :
    ∑ d ∈ (rad k).divisors, fP d = (k : ℝ) / k.totient := by
  have h1 := fPA_mult.prodPrimeFactors_one_add_of_squarefree (rad_sqf k)
  have h2 : ∑ d ∈ (rad k).divisors, fPA d = ∑ d ∈ (rad k).divisors, fP d := by
    refine sum_congr rfl fun d hd => ?_
    show (if d = 0 then 0 else fP d) = fP d
    rw [if_neg (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))]
  rw [← h2, ← h1, rad_pf]
  have h3 : ∀ p ∈ k.primeFactors, 1 + fPA p = (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    show 1 + (if p = 0 then 0 else fP p) = _
    rw [if_neg hpp.ne_zero]
    unfold fP
    rw [hpp.primeFactors, prod_singleton]
    have : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hne : (p : ℝ) - 1 ≠ 0 := by linarith
    rw [eq_div_iff hne, add_mul, one_div, inv_mul_cancel₀ hne]
    ring
  rw [prod_congr rfl h3, prod_div_distrib]
  have ht := Nat.totient_mul_prod_primeFactors k
  have hcast : ((∏ p ∈ k.primeFactors, (p - 1) : ℕ) : ℝ) = ∏ p ∈ k.primeFactors, ((p : ℝ) - 1) := by
    push_cast
    refine prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  have ht' : (k.totient : ℝ) * ∏ p ∈ k.primeFactors, (p : ℝ) =
      k * ∏ p ∈ k.primeFactors, ((p : ℝ) - 1) := by
    have ht2 : ((k.totient * ∏ p ∈ k.primeFactors, p : ℕ) : ℝ) =
        ((k * ∏ p ∈ k.primeFactors, (p - 1) : ℕ) : ℝ) := by rw [ht]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_prod, hcast] at ht2
    exact ht2
  have hφ : (k.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hk).ne'
  have hP : ∏ p ∈ k.primeFactors, ((p : ℝ) - 1) ≠ 0 := by
    rw [prod_ne_zero_iff]
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  rw [div_eq_div_iff hP hφ]
  linarith [ht']

private lemma dvd_rad {k ℓ : ℕ} (hk : k ≠ 0) (hℓ : ℓ.Prime) (h : ℓ ∣ k) : ℓ ∣ rad k :=
  dvd_prod_of_mem _ (Nat.mem_primeFactors.2 ⟨hℓ, h, hk⟩)

/-- Splitting off the part of `q` that divides `rad k`. -/
private theorem sum_sqf_le_coprime {k : ℕ} (hk : 1 ≤ k) (Q : ℕ) :
    ∑ q ∈ (Icc 1 Q).filter Squarefree, fP q ≤
      (k : ℝ) / k.totient * ∑ q ∈ (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q k), fP q := by
  set C := (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q k)
  set D := (rad k).divisors
  set g : ℕ → ℕ × ℕ := fun q => (Nat.gcd q (rad k), q / Nat.gcd q (rad k))
  have hk0 : k ≠ 0 := by omega
  have hsplit : ∀ q, Squarefree q → q ≠ 0 →
      q = (g q).1 * (g q).2 ∧ Nat.Coprime (g q).1 (g q).2 ∧ Squarefree (g q).2 := by
    intro q hq _
    have hq' : q = (g q).1 * (g q).2 := (Nat.mul_div_cancel' (Nat.gcd_dvd_left q (rad k))).symm
    refine ⟨hq', ?_⟩
    have := hq' ▸ hq
    rw [Nat.squarefree_mul_iff] at this
    exact ⟨this.1, this.2.2⟩
  have hmaps : ∀ q ∈ (Icc 1 Q).filter Squarefree, g q ∈ D ×ˢ C := by
    intro q hq
    rw [mem_filter, mem_Icc] at hq
    obtain ⟨heq, hcop, hsqf⟩ := hsplit q hq.2 (by omega)
    have hd0 : 0 < (g q).1 := Nat.gcd_pos_of_pos_left _ (by omega)
    rw [mem_product]
    refine ⟨Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right _ _, (rad_pos k).ne'⟩, ?_⟩
    rw [mem_filter, mem_Icc]
    have hq2pos : 0 < (g q).2 := by
      rcases Nat.eq_zero_or_pos (g q).2 with h | h
      · rw [h, mul_zero] at heq; omega
      · exact h
    have hq2le : (g q).2 ≤ q := Nat.div_le_self _ _
    refine ⟨⟨hq2pos, hq2le.trans hq.1.2⟩, hsqf, ?_⟩
    apply Nat.coprime_of_dvd
    intro ℓ hℓ h1 h2
    have hℓd : ℓ ∣ (g q).1 := by
      apply Nat.dvd_gcd
      · exact h1.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
      · exact dvd_rad hk0 hℓ h2
    have := Nat.dvd_gcd hℓd h1
    rw [hcop.gcd_eq_one] at this
    exact hℓ.one_lt.ne' (Nat.dvd_one.1 this)
  have hinj : Set.InjOn g ((Icc 1 Q).filter Squarefree) := by
    intro a ha b hb hab
    rw [mem_coe, mem_filter, mem_Icc] at ha hb
    rw [(hsplit a ha.2 (by omega)).1, (hsplit b hb.2 (by omega)).1, hab]
  have hval : ∀ q ∈ (Icc 1 Q).filter Squarefree, fP q = fP (g q).1 * fP (g q).2 := by
    intro q hq
    rw [mem_filter, mem_Icc] at hq
    obtain ⟨heq, hcop, -⟩ := hsplit q hq.2 (by omega)
    rw [← fP_mul hcop, ← heq]
  calc ∑ q ∈ (Icc 1 Q).filter Squarefree, fP q
      = ∑ q ∈ (Icc 1 Q).filter Squarefree, fP (g q).1 * fP (g q).2 := sum_congr rfl hval
    _ = ∑ y ∈ ((Icc 1 Q).filter Squarefree).image g, fP y.1 * fP y.2 :=
        (sum_image (f := fun y : ℕ × ℕ => fP y.1 * fP y.2) hinj).symm
    _ ≤ ∑ y ∈ D ×ˢ C, fP y.1 * fP y.2 := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro y hy
          obtain ⟨q, hq, rfl⟩ := mem_image.1 hy
          exact hmaps q hq
        · intro y _ _; exact mul_nonneg (fP_nonneg _) (fP_nonneg _)
    _ = (∑ d ∈ D, fP d) * ∑ q ∈ C, fP q := by rw [sum_mul_sum, sum_product]
    _ = _ := by rw [sum_divisors_rad_fP hk]

private lemma div_add_div_le (x y k : ℕ) (hk : 1 ≤ k) : (x + y) / k ≤ x / k + y / k + 1 := by
  have h1 := Nat.lt_mul_div_succ x (by omega : 0 < k)
  have h2 := Nat.lt_mul_div_succ y (by omega : 0 < k)
  have : x + y < k * (x / k + y / k + 2) := by nlinarith
  have := (Nat.div_lt_iff_lt_mul (by omega : 0 < k)).2 (by rw [mul_comm] at this; exact this)
  omega

/-- **Brun-Titchmarsh in progressions, explicit, from Montgomery's sieve.** -/
private theorem brun_titchmarsh_ap_montgomery (x y k r Q : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) :
    ((((Ioc x (x + y)).filter (fun p => p.Prime ∧ p % k = r % k)).card : ℕ) : ℝ) ≤
      Q + ((y / k : ℕ) + 2 + 2 * (Q : ℝ) ^ 2) * k / (k.totient * Real.log ((Q : ℝ) + 1)) := by
  set P := (Ioc x (x + y)).filter (fun p => p.Prime ∧ p % k = r % k)
  set Psmall := P.filter (· ≤ Q)
  set Pbig := P.filter (fun p => ¬ p ≤ Q)
  have hsplit : P.card = Psmall.card + Pbig.card := (card_filter_add_card_filter_not _).symm
  have hsmall : (Psmall.card : ℝ) ≤ Q := by
    have : Psmall ⊆ Icc 1 Q := by
      intro p hp
      simp only [Psmall, P, mem_filter, mem_Ioc] at hp
      exact mem_Icc.2 ⟨hp.1.2.1.one_lt.le, hp.2⟩
    have := card_le_card this
    rw [Nat.card_Icc] at this
    exact_mod_cast (by omega : Psmall.card ≤ Q)
  set r' := r % k
  have hdecomp : ∀ p ∈ Pbig, p = k * (p / k) + r' := by
    intro p hp
    simp only [Pbig, P, mem_filter] at hp
    show p = k * (p / k) + r % k
    rw [← hp.1.2.2]; exact (Nat.div_add_mod p k).symm
  set A : Finset ℤ := Pbig.image (fun p : ℕ => ((p / k : ℕ) : ℤ))
  have hAcard : A.card = Pbig.card := by
    apply card_image_of_injOn
    intro a ha b hb hab
    simp only [Nat.cast_inj] at hab
    rw [hdecomp a ha, hdecomp b hb, hab]
  set M : ℤ := ((x / k : ℕ) : ℤ) - 1
  set N : ℕ := y / k + 2
  have hA : A ⊆ Ioc M (M + N) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hn
    simp only [Pbig, P, mem_filter, mem_Ioc] at hp
    have h1 : x / k ≤ p / k := Nat.div_le_div_right hp.1.1.1.le
    have h2 : p / k ≤ (x + y) / k := Nat.div_le_div_right hp.1.1.2
    have h3 := div_add_div_le x y k hk
    rw [mem_Ioc]
    simp only [M, N]
    constructor <;> push_cast <;> omega
  -- the forbidden class modulo a prime not dividing `k`
  set b : ℕ → ℕ := fun ℓ => ((-(r' : ZMod ℓ)) * (k : ZMod ℓ)⁻¹).val
  set B : ℕ → Finset ℕ := fun ℓ => if ℓ ∣ k then ∅ else {b ℓ}
  have hB : ∀ ℓ, ℓ.Prime → B ℓ ⊆ range ℓ ∧ (B ℓ).card < ℓ := by
    intro ℓ hℓ
    have : NeZero ℓ := ⟨hℓ.ne_zero⟩
    simp only [B]
    split_ifs
    · exact ⟨empty_subset _, by rw [card_empty]; exact hℓ.pos⟩
    · refine ⟨?_, by rw [card_singleton]; exact hℓ.one_lt⟩
      intro c hc
      rw [mem_singleton] at hc
      rw [hc, mem_range]
      exact ZMod.val_lt _
  have hAB : ∀ ℓ, ℓ.Prime → ℓ ≤ Q → ∀ n ∈ A, (n % (ℓ : ℤ)).toNat ∉ B ℓ := by
    intro ℓ hℓ hℓQ n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hn
    have hpd := hdecomp p hp
    simp only [Pbig, P, mem_filter, mem_Ioc] at hp
    simp only [B]
    split_ifs with hdvd
    · exact Finset.notMem_empty _
    rw [mem_singleton, ← Int.natCast_mod, Int.toNat_natCast]
    intro hmod
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have hk0 : (k : ZMod ℓ) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact hdvd
    have hcast : ((p / k : ℕ) : ZMod ℓ) = (-(r' : ZMod ℓ)) * (k : ZMod ℓ)⁻¹ := by
      rw [← ZMod.natCast_mod, hmod, ZMod.natCast_zmod_val]
    have hp0 : (p : ZMod ℓ) = 0 := by
      rw [hpd]
      push_cast
      have hu : (k : ZMod ℓ) * (k : ZMod ℓ)⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _
          ((ZMod.isUnit_iff_coprime k ℓ).2 ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hdvd).symm)
      rw [hcast, mul_comm (-(r' : ZMod ℓ)), ← mul_assoc, hu]
      ring
    rw [ZMod.natCast_eq_zero_iff] at hp0
    have := (Nat.prime_dvd_prime_iff_eq hℓ hp.1.2.1).1 hp0
    omega
  have hmont := montgomery_sieve hQ M N A hA B hB hAB
  -- lower bound for the sieve sum
  have hW_ge : ∑ q ∈ (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q k), fP q ≤
      ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q := by
    have hsub : (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q k) ⊆
        (Icc 1 Q).filter Squarefree := by
      intro q hq; rw [mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.1⟩
    have heq : ∀ q ∈ (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q k),
        fP q = hW B q := by
      intro q hq
      rw [mem_filter, mem_Icc] at hq
      unfold fP hW
      refine prod_congr rfl fun ℓ hℓ => ?_
      have hℓk : ¬ ℓ ∣ k := by
        intro h
        have := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hℓ) h
        rw [hq.2.2.gcd_eq_one] at this
        exact (Nat.prime_of_mem_primeFactors hℓ).one_lt.ne' (Nat.dvd_one.1 this)
      simp only [B, if_neg hℓk, card_singleton, Nat.cast_one]
    rw [sum_congr rfl heq]
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro q _ _
    unfold hW
    refine prod_nonneg fun ℓ hℓ => ?_
    have hℓp := Nat.prime_of_mem_primeFactors hℓ
    have := (hB ℓ hℓp).2
    have : ((B ℓ).card : ℝ) < ℓ := by exact_mod_cast this
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hlog := log_le_sum_sqf Q
  have hfP : ∀ q : ℕ, ∏ p ∈ q.primeFactors, 1 / (((p : ℕ) : ℝ) - 1) = fP q := fun q => rfl
  simp_rw [hfP] at hlog
  have hcop := sum_sqf_le_coprime hk Q
  have hlogpos : 0 < Real.log ((Q : ℝ) + 1) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hφ : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.2 hk
  -- `φ(k)/k · log(Q + 1) ≤ ∑ hW`
  have hL : (k.totient : ℝ) * Real.log ((Q : ℝ) + 1) ≤
      k * ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q := by
    have h1 : Real.log ((Q : ℝ) + 1) ≤ (k : ℝ) / k.totient *
        ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q :=
      (hlog.trans hcop).trans (mul_le_mul_of_nonneg_left hW_ge (by positivity))
    rw [div_mul_eq_mul_div, le_div_iff₀ hφ] at h1
    linarith
  have hbig : (Pbig.card : ℝ) ≤
      ((y / k : ℕ) + 2 + 2 * (Q : ℝ) ^ 2) * k / (k.totient * Real.log ((Q : ℝ) + 1)) := by
    rw [le_div_iff₀ (by positivity), ← hAcard]
    have hm : (A.card : ℝ) * ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q ≤
        (y / k : ℕ) + 2 + 2 * (Q : ℝ) ^ 2 := by
      have := hmont; simp only [N] at this; push_cast at this ⊢; linarith
    calc (A.card : ℝ) * (k.totient * Real.log ((Q : ℝ) + 1))
        ≤ (A.card : ℝ) * (k * ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q) :=
          mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg _)
      _ = k * ((A.card : ℝ) * ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q) := by ring
      _ ≤ k * ((y / k : ℕ) + 2 + 2 * (Q : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hm hk'.le
      _ = _ := by ring
  rw [hsplit, Nat.cast_add]
  linarith


end

/-! ### copied from PNTPort/LargeSieve/MontgomeryTau.lean -/
section

/-!
# The divisor-weighted sieve sum for two residue classes

Lab proof, unit U-5554, CLOUD 20261019T1321Z-cloud25. AI wrote this file. Known mathematics.

With `c(ℓ) = (2ℓ - 1)/(ℓ - 1)² = ∑_{k ≥ 1} (k + 1) ℓ^{-k}`:

* `sum_tau_pf_eq_le`: `∑_{n ≤ Q, primeFactors n = P} τ(n)/n ≤ ∏_{ℓ ∈ P} c(ℓ)`.
* `sum_tau_le_sum_sqf`: `∑_{n ≤ Q} τ(n)/n ≤ ∑_{q ≤ Q squarefree} ∏_{ℓ ∣ q} c(ℓ)`.
* `sum_tau_ge`: `∑_{n ≤ Q} τ(n)/n ≥ log²(Q + 1)/2 - 3/4` for `Q ≥ 3`.
* `sum_sqf_c_le_coprime`: `∑_{q ≤ Q sqf} ∏ c ≤ (k/φ(k))² ∑_{q ≤ Q sqf, (q, k) = 1} ∏ c`, since
  `1 + c(ℓ) = (ℓ/(ℓ - 1))²`.
-/


open Finset Real

/-- `c(ℓ) = (2ℓ - 1)/(ℓ - 1)²`. -/
private noncomputable def cW (ℓ : ℕ) : ℝ := (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2

/-- `τ(n)` as a real number. -/
private noncomputable def tau (n : ℕ) : ℝ := (n.divisors.card : ℝ)

private lemma tau_mul {m n : ℕ} (h : Nat.Coprime m n) : tau (m * n) = tau m * tau n := by
  unfold tau; rw [Nat.Coprime.card_divisors_mul h]; push_cast; ring

private lemma tau_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : tau (p ^ k) = k + 1 := by
  unfold tau
  rw [← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  push_cast; ring

private lemma tau_nonneg (n : ℕ) : 0 ≤ tau n := Nat.cast_nonneg _

private lemma geom_tau_le {p : ℕ} (hp : p.Prime) (Q : ℕ) :
    ∑ k ∈ Icc 1 Q, ((k : ℝ) + 1) * (1 / (p : ℝ)) ^ k ≤ cW p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  set x : ℝ := 1 / (p : ℝ)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by simp only [x]; rw [div_lt_one (by linarith)]; linarith
  have hnx : ‖x‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hnx
  have h2 := hasSum_geometric_of_lt_one hx0 hx1
  have h3 := h1.add h2
  have hle := sum_le_hasSum (range (Q + 1)) (fun k _ => by positivity) h3
  have hsplit : ∑ k ∈ range (Q + 1), ((k : ℝ) * x ^ k + x ^ k) =
      1 + ∑ k ∈ Icc 1 Q, ((k : ℝ) + 1) * x ^ k := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
    simp only [Nat.cast_zero, zero_mul, pow_zero, zero_add]
    congr 1
    rw [show Ico 1 (Q + 1) = Icc 1 Q by ext; simp]
    refine sum_congr rfl fun k _ => by ring
  rw [hsplit] at hle
  have hval : x / (1 - x) ^ 2 + (1 - x)⁻¹ - 1 = cW p := by
    simp only [x, cW]
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    have h1p : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / p := by field_simp
    rw [h1p]
    field_simp
    ring
  linarith

/-- The divisor-weighted fibre of `n ↦ primeFactors n`. -/
private theorem sum_tau_pf_eq_le (Q : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ n ∈ (Icc 1 Q).filter (fun n => n.primeFactors = P), tau n / n ≤ ∏ p ∈ P, cW p := by
  induction P using Finset.induction_on with
  | empty =>
    rw [prod_empty]
    have : (Icc 1 Q).filter (fun n => n.primeFactors = ∅) ⊆ {1} := by
      intro n hn
      rw [mem_filter, Nat.primeFactors_eq_empty, mem_Icc] at hn
      rw [mem_singleton]; omega
    refine (sum_le_sum_of_subset_of_nonneg this
      (fun _ _ _ => div_nonneg (tau_nonneg _) (Nat.cast_nonneg _))).trans ?_
    simp [tau]
  | insert p P' hpP' ih =>
    have hp : p.Prime := hP p (mem_insert_self _ _)
    have hP' : ∀ r ∈ P', r.Prime := fun r hr => hP r (mem_insert_of_mem hr)
    set T' := (Icc 1 Q).filter (fun n => n.primeFactors = P')
    have hsub : (Icc 1 Q).filter (fun n => n.primeFactors = insert p P') ⊆
        (Icc 1 Q ×ˢ T').image (fun km : ℕ × ℕ => p ^ km.1 * km.2) := by
      intro n hn
      rw [mem_filter, mem_Icc] at hn
      obtain ⟨⟨hn1, hnQ⟩, hpf⟩ := hn
      have hn0 : n ≠ 0 := by omega
      have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors (by rw [hpf]; exact mem_insert_self _ _)
      set k := n.factorization p
      have hk1 : 1 ≤ k := hp.factorization_pos_of_dvd hn0 hpn
      have hpk : p ^ k ∣ n := Nat.ordProj_dvd n p
      have hkQ : k ≤ Q := by
        have := Nat.lt_pow_self hp.one_lt (n := k)
        have := Nat.le_of_dvd (by omega) hpk
        omega
      set m := n / p ^ k
      have hm0 : 0 < m := Nat.ordCompl_pos p hn0
      have hmQ : m ≤ Q := (Nat.div_le_self n _).trans hnQ
      have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp hn0
      have hmn : n = p ^ k * m := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
      have hpfm : m.primeFactors = P' := by
        ext r
        constructor
        · intro hr
          have hrn : r ∈ n.primeFactors :=
            Nat.primeFactors_mono (Nat.ordCompl_dvd n p) hn0 hr
          rw [hpf, mem_insert] at hrn
          rcases hrn with rfl | h
          · exact absurd (Nat.dvd_of_mem_primeFactors hr)
              ((Nat.Prime.coprime_iff_not_dvd hp).1 hcop)
          · exact h
        · intro hr
          have hrn : r ∈ n.primeFactors := by rw [hpf]; exact mem_insert_of_mem hr
          have hrp : r ≠ p := fun h => hpP' (h ▸ hr)
          have hrprime := hP' r hr
          have hcr : Nat.Coprime r (p ^ k) :=
            Nat.Coprime.pow_right k ((Nat.coprime_primes hrprime hp).2 hrp)
          have hrd : r ∣ p ^ k * m := hmn ▸ Nat.dvd_of_mem_primeFactors hrn
          exact Nat.mem_primeFactors.2 ⟨hrprime, hcr.dvd_of_dvd_mul_left hrd, hm0.ne'⟩
      refine mem_image.2 ⟨(k, m), ?_, hmn.symm⟩
      rw [mem_product, mem_Icc]
      exact ⟨⟨hk1, hkQ⟩, mem_filter.2 ⟨mem_Icc.2 ⟨hm0, hmQ⟩, hpfm⟩⟩
    have hterm : ∀ km ∈ Icc 1 Q ×ˢ T', tau (p ^ km.1 * km.2) / ((p ^ km.1 * km.2 : ℕ) : ℝ) =
        (((km.1 : ℝ) + 1) * (1 / (p : ℝ)) ^ km.1) * (tau km.2 / km.2) := by
      intro km hkm
      rw [mem_product, mem_filter] at hkm
      have hcop : Nat.Coprime (p ^ km.1) km.2 := by
        apply Nat.Coprime.pow_left
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hd
        have hm0 : km.2 ≠ 0 := by have := (mem_Icc.1 hkm.2.1).1; omega
        have : p ∈ km.2.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hd, hm0⟩
        rw [hkm.2.2] at this
        exact hpP' this
      rw [tau_mul hcop, tau_prime_pow hp]
      push_cast
      rw [one_div_pow]
      field_simp
    calc ∑ n ∈ (Icc 1 Q).filter (fun n => n.primeFactors = insert p P'), tau n / n
        ≤ ∑ n ∈ (Icc 1 Q ×ˢ T').image (fun km : ℕ × ℕ => p ^ km.1 * km.2), tau n / n :=
          sum_le_sum_of_subset_of_nonneg hsub
            (fun _ _ _ => div_nonneg (tau_nonneg _) (Nat.cast_nonneg _))
      _ ≤ ∑ km ∈ Icc 1 Q ×ˢ T', tau (p ^ km.1 * km.2) / ((p ^ km.1 * km.2 : ℕ) : ℝ) :=
          sum_image_le_of_nonneg' _ _ (fun n : ℕ => tau n / n)
            (fun _ => div_nonneg (tau_nonneg _) (Nat.cast_nonneg _))
      _ = (∑ k ∈ Icc 1 Q, ((k : ℝ) + 1) * (1 / (p : ℝ)) ^ k) * ∑ m ∈ T', tau m / m := by
          rw [sum_congr rfl hterm, sum_mul_sum, sum_product]
      _ ≤ cW p * ∏ r ∈ P', cW r := by
          apply mul_le_mul (geom_tau_le hp Q) (ih hP')
            (sum_nonneg fun _ _ => div_nonneg (tau_nonneg _) (Nat.cast_nonneg _))
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
          unfold cW; exact div_nonneg (by linarith) (by positivity)
      _ = ∏ r ∈ insert p P', cW r := by rw [prod_insert hpP']

/-- `∑_{n ≤ Q} τ(n)/n ≤ ∑_{q ≤ Q sqf} ∏_{ℓ ∣ q} c(ℓ)`. -/
private theorem sum_tau_le_sum_sqf (Q : ℕ) :
    ∑ n ∈ Icc 1 Q, tau n / n ≤ ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, cW p := by
  rw [← sum_fiberwise_of_maps_to (s := Icc 1 Q) (t := (Icc 1 Q).filter Squarefree) (g := rad)
    (fun n hn => by
      rw [mem_Icc] at hn
      refine mem_filter.2 ⟨mem_Icc.2 ⟨rad_pos n, ?_⟩, rad_sqf n⟩
      exact (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)).trans hn.2)]
  refine sum_le_sum fun q _ => ?_
  have hsub : (Icc 1 Q).filter (fun n => rad n = q) ⊆
      (Icc 1 Q).filter (fun n => n.primeFactors = q.primeFactors) := by
    intro n hn
    rw [mem_filter] at hn ⊢
    exact ⟨hn.1, by rw [← rad_pf n, hn.2]⟩
  exact (sum_le_sum_of_subset_of_nonneg hsub
    (fun _ _ _ => div_nonneg (tau_nonneg _) (Nat.cast_nonneg _))).trans
    (sum_tau_pf_eq_le Q _ (fun p hp => Nat.prime_of_mem_primeFactors hp))

/-- `∑_{n ≤ Q} τ(n)/n = ∑_{a ≤ Q} (1/a) ∑_{b ≤ Q/a} 1/b`. -/
private lemma sum_tau_eq (Q : ℕ) :
    ∑ n ∈ Icc 1 Q, tau n / n = ∑ a ∈ Icc 1 Q, (1 / (a : ℝ)) * ∑ b ∈ Icc 1 (Q / a), 1 / (b : ℝ) := by
  have h1 : ∀ n ∈ Icc 1 Q, tau n / n = ∑ x ∈ n.divisorsAntidiagonal, 1 / ((x.1 : ℝ) * x.2) := by
    intro n hn
    unfold tau
    rw [← Nat.map_div_right_divisors, sum_map, card_eq_sum_ones, Nat.cast_sum, sum_div]
    refine sum_congr rfl fun d hd => ?_
    show ((1 : ℕ) : ℝ) / n = 1 / ((d : ℝ) * ((n / d : ℕ) : ℝ))
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd), Nat.cast_one]
  rw [sum_congr rfl h1, sum_sigma']
  simp_rw [mul_sum]
  rw [sum_sigma']
  refine sum_bij' (fun x _ => ⟨x.2.1, x.2.2⟩) (fun x _ => ⟨x.1 * x.2, (x.1, x.2)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, a, b⟩ h
    simp only [mem_sigma, mem_Icc, Nat.mem_divisorsAntidiagonal] at h ⊢
    obtain ⟨⟨h1, h2⟩, h3, -⟩ := h
    have ha : 1 ≤ a := Nat.pos_of_ne_zero (by rintro rfl; simp at h3; omega)
    have hb : 1 ≤ b := Nat.pos_of_ne_zero (by rintro rfl; simp at h3; omega)
    refine ⟨⟨ha, ?_⟩, hb, ?_⟩
    · calc a ≤ a * b := Nat.le_mul_of_pos_right a hb
        _ ≤ Q := h3 ▸ h2
    · rw [Nat.le_div_iff_mul_le ha]; rw [mul_comm]; exact h3 ▸ h2
  · rintro ⟨a, b⟩ h
    simp only [mem_sigma, mem_Icc, Nat.mem_divisorsAntidiagonal] at h ⊢
    obtain ⟨⟨h1, -⟩, h3, h4⟩ := h
    rw [Nat.le_div_iff_mul_le h1] at h4
    refine ⟨⟨Nat.mul_pos h1 h3, by rw [mul_comm]; exact h4⟩, ?_⟩
    try simp only [true_and]
    positivity
  · rintro ⟨n, a, b⟩ h
    simp only [mem_sigma, Nat.mem_divisorsAntidiagonal] at h
    simp [h.2.1]
  · rintro ⟨a, b⟩ _; rfl
  · rintro ⟨n, a, b⟩ _
    simp only
    rw [one_div_mul_one_div]

private lemma sum_log_div_le (Q : ℕ) (hQ : 3 ≤ Q) :
    ∑ a ∈ Icc 1 Q, Real.log (a : ℝ) / (a : ℝ) ≤ Real.log Q ^ 2 / 2 + 3 / 4 := by
  have hsplit : Icc 1 Q = (Icc 1 3 : Finset ℕ) ∪ Ico 4 (Q + 1) := by
    ext a; simp only [mem_Icc, mem_union, mem_Ico]; omega
  have hdisj : Disjoint (Icc 1 3 : Finset ℕ) (Ico 4 (Q + 1)) := by
    rw [disjoint_left]; intro a ha hb
    simp only [mem_Icc, mem_Ico] at ha hb; omega
  have hsmall : ∑ a ∈ (Icc 1 3 : Finset ℕ), Real.log (a : ℝ) / (a : ℝ) ≤ 3 / 4 := by
    rw [show (Icc 1 3 : Finset ℕ) = {1, 2, 3} by decide]
    rw [sum_insert (by decide), sum_insert (by decide), sum_singleton]
    simp only [Nat.cast_one, Real.log_one, zero_div, zero_add, Nat.cast_ofNat]
    have h2 : Real.log 2 < 0.6932 := Real.log_two_lt_d9.trans (by norm_num)
    have h32 : Real.log (3 / 2) ≤ 3 / 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h3 : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    rw [h3]
    linarith
  have hanti : AntitoneOn (fun x : ℝ => Real.log x / x) (Set.Icc ((3 : ℕ) : ℝ) ((Q : ℕ) : ℝ)) := by
    apply Real.log_div_self_antitoneOn.mono
    intro x hx
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Ici]
    have he := Real.exp_one_lt_three
    push_cast at hx
    linarith [hx.1]
  have htail := AntitoneOn.sum_le_integral_Ico hQ hanti
  have hx3 : ∀ x ∈ Set.uIcc ((3 : ℕ) : ℝ) ((Q : ℕ) : ℝ), (3 : ℝ) ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le (by exact_mod_cast hQ)] at hx
    push_cast at hx; exact hx.1
  have hint : ∫ x in ((3 : ℕ) : ℝ)..((Q : ℕ) : ℝ), Real.log x / x =
      Real.log Q ^ 2 / 2 - Real.log 3 ^ 2 / 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => Real.log x ^ 2 / 2)]
    · push_cast; ring
    · intro x hx
      have hx0 : 0 < x := by linarith [hx3 x hx]
      have := ((Real.hasDerivAt_log hx0.ne').pow 2).div_const 2
      convert this using 1
      field_simp
      ring
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div (Real.continuousOn_log.mono ?_) continuousOn_id
      · intro x hx h
        have := hx3 x hx
        have h0 : x = 0 := h
        linarith
      · intro x hx h
        have := hx3 x hx
        have h0 : x = 0 := h
        linarith
  rw [hint] at htail
  have hshift := Finset.sum_Ico_add' (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) 3 Q 1
  have hlog3 : 0 ≤ Real.log 3 ^ 2 / 2 := by positivity
  have htail' : ∑ a ∈ Ico 4 (Q + 1), Real.log (a : ℝ) / (a : ℝ) ≤ Real.log Q ^ 2 / 2 := by
    have : ∑ a ∈ Ico 4 (Q + 1), Real.log (a : ℝ) / (a : ℝ) =
        ∑ i ∈ Ico 3 Q, Real.log (((i + 1 : ℕ) : ℝ)) / (((i + 1 : ℕ) : ℝ)) := hshift.symm
    rw [this]
    linarith
  rw [hsplit, sum_union hdisj]
  linarith

/-- `∑_{n ≤ Q} τ(n)/n ≥ log²(Q + 1)/2 - 3/4` for `Q ≥ 3`. -/
private theorem sum_tau_ge (Q : ℕ) (hQ : 3 ≤ Q) :
    Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4 ≤ ∑ n ∈ Icc 1 Q, tau n / n := by
  rw [sum_tau_eq]
  have hinner : ∀ a ∈ Icc 1 Q, Real.log (((Q : ℝ) + 1) / a) ≤ ∑ b ∈ Icc 1 (Q / a), 1 / (b : ℝ) := by
    intro a ha
    rw [mem_Icc] at ha
    have hH := log_add_one_le_harmonic (Q / a)
    rw [harmonic_eq_sum_Icc] at hH
    push_cast at hH
    simp_rw [one_div]
    refine le_trans ?_ hH
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha.1
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ ha0]
    have : Q + 1 ≤ (Q / a + 1) * a := by
      have := Nat.lt_mul_div_succ Q (by omega : 0 < a); rw [mul_comm] at this; omega
    exact_mod_cast this
  have hlow : ∑ a ∈ Icc 1 Q, (1 / (a : ℝ)) * Real.log (((Q : ℝ) + 1) / a) ≤
      ∑ a ∈ Icc 1 Q, (1 / (a : ℝ)) * ∑ b ∈ Icc 1 (Q / a), 1 / (b : ℝ) :=
    sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hinner a ha) (by positivity)
  refine le_trans ?_ hlow
  have hexp : ∑ a ∈ Icc 1 Q, (1 / (a : ℝ)) * Real.log (((Q : ℝ) + 1) / a) =
      Real.log ((Q : ℝ) + 1) * ∑ a ∈ Icc 1 Q, 1 / (a : ℝ) - ∑ a ∈ Icc 1 Q, Real.log a / a := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun a ha => ?_
    rw [mem_Icc] at ha
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha.1
    rw [Real.log_div (by positivity) ha0.ne']
    ring
  rw [hexp]
  have hH := log_add_one_le_harmonic Q
  rw [harmonic_eq_sum_Icc] at hH
  push_cast at hH
  simp_rw [← one_div] at hH
  have hL0 : 0 ≤ Real.log ((Q : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg Q : (0 : ℝ) ≤ Q)])
  have h1 : Real.log ((Q : ℝ) + 1) ^ 2 ≤ Real.log ((Q : ℝ) + 1) * ∑ a ∈ Icc 1 Q, 1 / (a : ℝ) := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hH hL0
  have h2 := sum_log_div_le Q hQ
  have h3 : Real.log Q ≤ Real.log ((Q : ℝ) + 1) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < Q)) (by linarith)
  have h4 : Real.log Q ^ 2 ≤ Real.log ((Q : ℝ) + 1) ^ 2 := by
    have : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q))
    nlinarith
  linarith

/-- `∏_{ℓ ∣ q} c(ℓ)`. -/
private noncomputable def fC (q : ℕ) : ℝ := ∏ p ∈ q.primeFactors, cW p

private lemma cW_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ cW p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold cW; exact div_nonneg (by linarith) (by positivity)

private lemma fC_nonneg (q : ℕ) : 0 ≤ fC q :=
  prod_nonneg fun _ hp => cW_nonneg (Nat.prime_of_mem_primeFactors hp)

private lemma fC_mul {m n : ℕ} (h : Nat.Coprime m n) : fC (m * n) = fC m * fC n := by
  unfold fC
  rw [Nat.Coprime.primeFactors_mul h, prod_union h.disjoint_primeFactors]

private noncomputable def fCA : ArithmeticFunction ℝ := ⟨fun d => if d = 0 then 0 else fC d, by simp⟩

private lemma fCA_mult : fCA.IsMultiplicative := by
  refine ⟨by simp [fCA, fC], fun {m n} h => ?_⟩
  show (if m * n = 0 then 0 else fC (m * n)) = (if m = 0 then 0 else fC m) * (if n = 0 then 0 else fC n)
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn, fC_mul h]

/-- `∑_{d ∣ rad k} fC d = (k/φ(k))²`. -/
private theorem sum_divisors_rad_fC {k : ℕ} (hk : 1 ≤ k) :
    ∑ d ∈ (rad k).divisors, fC d = ((k : ℝ) / k.totient) ^ 2 := by
  have h1 := fCA_mult.prodPrimeFactors_one_add_of_squarefree (rad_sqf k)
  have h2 : ∑ d ∈ (rad k).divisors, fCA d = ∑ d ∈ (rad k).divisors, fC d := by
    refine sum_congr rfl fun d hd => ?_
    show (if d = 0 then 0 else fC d) = fC d
    rw [if_neg (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))]
  rw [← h2, ← h1, rad_pf]
  have h3 : ∀ p ∈ k.primeFactors, 1 + fCA p = ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    show 1 + (if p = 0 then 0 else fC p) = _
    rw [if_neg hpp.ne_zero]
    unfold fC cW
    rw [hpp.primeFactors, prod_singleton]
    have : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hne : (p : ℝ) - 1 ≠ 0 := by linarith
    rw [div_pow, eq_div_iff (pow_ne_zero 2 hne), add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hne)]
    ring
  rw [prod_congr rfl h3, prod_pow]
  congr 1
  rw [← sum_divisors_rad_fP hk]
  have h4 := fPA_mult.prodPrimeFactors_one_add_of_squarefree (rad_sqf k)
  have h5 : ∑ d ∈ (rad k).divisors, fPA d = ∑ d ∈ (rad k).divisors, fP d := by
    refine sum_congr rfl fun d hd => ?_
    show (if d = 0 then 0 else fP d) = fP d
    rw [if_neg (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))]
  rw [← h5, ← h4, rad_pf]
  refine prod_congr rfl fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  show _ = 1 + (if p = 0 then 0 else fP p)
  rw [if_neg hpp.ne_zero]
  unfold fP
  rw [hpp.primeFactors, prod_singleton]
  have : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
  have hne : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [eq_comm, eq_div_iff hne, add_mul, one_div, inv_mul_cancel₀ hne]
  ring

/-- Splitting off the part of `q` that divides `rad k`, for the weight `fC`. -/
private theorem sum_sqf_c_le_coprime {k : ℕ} (hk : 1 ≤ k) (Q : ℕ) :
    ∑ q ∈ (Icc 1 Q).filter Squarefree, fC q ≤
      ((k : ℝ) / k.totient) ^ 2 *
        ∑ q ∈ (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q k), fC q := by
  set C := (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q k)
  set D := (rad k).divisors
  set g : ℕ → ℕ × ℕ := fun q => (Nat.gcd q (rad k), q / Nat.gcd q (rad k))
  have hk0 : k ≠ 0 := by omega
  have hsplit : ∀ q, Squarefree q →
      q = (g q).1 * (g q).2 ∧ Nat.Coprime (g q).1 (g q).2 ∧ Squarefree (g q).2 := by
    intro q hq
    have hq' : q = (g q).1 * (g q).2 := (Nat.mul_div_cancel' (Nat.gcd_dvd_left q (rad k))).symm
    refine ⟨hq', ?_⟩
    have := hq' ▸ hq
    rw [Nat.squarefree_mul_iff] at this
    exact ⟨this.1, this.2.2⟩
  have hmaps : ∀ q ∈ (Icc 1 Q).filter Squarefree, g q ∈ D ×ˢ C := by
    intro q hq
    rw [mem_filter, mem_Icc] at hq
    obtain ⟨heq, hcop, hsqf⟩ := hsplit q hq.2
    rw [mem_product]
    refine ⟨Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right _ _, (rad_pos k).ne'⟩, ?_⟩
    rw [mem_filter, mem_Icc]
    have hq2pos : 0 < (g q).2 := by
      rcases Nat.eq_zero_or_pos (g q).2 with h | h
      · rw [h, mul_zero] at heq; omega
      · exact h
    refine ⟨⟨hq2pos, (Nat.div_le_self _ _).trans hq.1.2⟩, hsqf, ?_⟩
    apply Nat.coprime_of_dvd
    intro ℓ hℓ h1 h2
    have hℓd : ℓ ∣ (g q).1 := by
      apply Nat.dvd_gcd
      · exact h1.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
      · exact dvd_rad hk0 hℓ h2
    have := Nat.dvd_gcd hℓd h1
    rw [hcop.gcd_eq_one] at this
    exact hℓ.one_lt.ne' (Nat.dvd_one.1 this)
  have hinj : Set.InjOn g ((Icc 1 Q).filter Squarefree) := by
    intro a ha b hb hab
    rw [mem_coe, mem_filter] at ha hb
    rw [(hsplit a ha.2).1, (hsplit b hb.2).1, hab]
  have hval : ∀ q ∈ (Icc 1 Q).filter Squarefree, fC q = fC (g q).1 * fC (g q).2 := by
    intro q hq
    rw [mem_filter] at hq
    obtain ⟨heq, hcop, -⟩ := hsplit q hq.2
    rw [← fC_mul hcop, ← heq]
  calc ∑ q ∈ (Icc 1 Q).filter Squarefree, fC q
      = ∑ q ∈ (Icc 1 Q).filter Squarefree, fC (g q).1 * fC (g q).2 := sum_congr rfl hval
    _ = ∑ y ∈ ((Icc 1 Q).filter Squarefree).image g, fC y.1 * fC y.2 :=
        (sum_image (f := fun y : ℕ × ℕ => fC y.1 * fC y.2) hinj).symm
    _ ≤ ∑ y ∈ D ×ˢ C, fC y.1 * fC y.2 := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro y hy
          obtain ⟨q, hq, rfl⟩ := mem_image.1 hy
          exact hmaps q hq
        · intro y _ _; exact mul_nonneg (fC_nonneg _) (fC_nonneg _)
    _ = (∑ d ∈ D, fC d) * ∑ q ∈ C, fC q := by rw [sum_mul_sum, sum_product]
    _ = _ := by rw [sum_divisors_rad_fC hk]


end

/-! ### copied from PNTPort/LargeSieve/MontgomeryGoldbach.lean -/
section

/-!
# An explicit upper bound for the Goldbach count from Montgomery's sieve

Lab proof, unit U-5554, CLOUD 20261019T1321Z-cloud25. AI wrote this file. Known mathematics, the
upper bound sieve for `r(N) = #{p ≤ N : p, N - p prime}`; the order `N/log² N` is Brun 1920.
No cited input. Binary Goldbach is OPEN; this is an upper bound for the number of
representations, not a lower bound.

* `goldbach_upper_montgomery`: for even `N ≥ 4` and `Q ≥ 3`,
  `r(N) ≤ 2Q + (N + 2Q²) (N/φ(N))² / (log²(Q + 1)/2 - 3/4)`.
  With `Q` near `√N / log N` this is `r(N) ≤ (8 + o(1)) (N/φ(N))² N / log² N`.

The sieve: modulo a prime `ℓ ≤ Q`, a prime `p > Q` with `N - p > Q` prime misses the classes
`0` and `N mod ℓ`. The sieve sum is bounded below through the weight
`c(ℓ) = (2ℓ - 1)/(ℓ - 1)² ≤ 2/(ℓ - 2)` and `∑_{n ≤ Q} τ(n)/n`, after removing the primes of `N`
at the cost `(N/φ(N))²`.
-/


open Finset Real

private lemma cW_le_two_div {ℓ : ℕ} (hℓ : 3 ≤ ℓ) : cW ℓ ≤ 2 / ((ℓ : ℝ) - 2) := by
  have h3 : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  unfold cW
  rw [div_le_div_iff₀ (by nlinarith) (by linarith)]
  nlinarith

/-- **Upper bound for the Goldbach count, explicit, from Montgomery's sieve.** -/
private theorem goldbach_upper_montgomery (N Q : ℕ) (hN : Even N) (hN4 : 4 ≤ N) (hQ : 3 ≤ Q) :
    ((((range (N + 1)).filter (fun p => p.Prime ∧ (N - p).Prime)).card : ℕ) : ℝ) ≤
      2 * Q + (N + 2 * (Q : ℝ) ^ 2) * ((N : ℝ) / N.totient) ^ 2 /
        (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4) := by
  set P := (range (N + 1)).filter (fun p => p.Prime ∧ (N - p).Prime)
  set Pbig := P.filter (fun p => Q < p ∧ Q < N - p)
  set Psmall := P.filter (fun p => ¬ (Q < p ∧ Q < N - p))
  have hsplit : P.card = Pbig.card + Psmall.card := (card_filter_add_card_filter_not _).symm
  have hsmall : (Psmall.card : ℝ) ≤ 2 * Q := by
    have hsub : Psmall ⊆ (Icc 1 Q) ∪ (Icc 1 Q).image (fun m => N - m) := by
      intro p hp
      simp only [Psmall, P, mem_filter, mem_range, not_and_or, not_lt] at hp
      obtain ⟨⟨hpN, hpp, hqp⟩, h⟩ := hp
      rw [mem_union]
      rcases h with h | h
      · exact Or.inl (mem_Icc.2 ⟨hpp.one_lt.le, h⟩)
      · refine Or.inr (mem_image.2 ⟨N - p, mem_Icc.2 ⟨hqp.one_lt.le, h⟩, by omega⟩)
    have := (card_le_card hsub).trans (card_union_le _ _)
    have h2 := card_image_le (s := Icc 1 Q) (f := fun m => N - m)
    rw [Nat.card_Icc] at this h2
    exact_mod_cast (by omega : Psmall.card ≤ 2 * Q)
  set A : Finset ℤ := Pbig.image (fun p : ℕ => (p : ℤ))
  have hAcard : A.card = Pbig.card := card_image_of_injective _ Nat.cast_injective
  have hA : A ⊆ Ioc (0 : ℤ) (0 + (N : ℕ)) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hn
    simp only [Pbig, P, mem_filter, mem_range] at hp
    rw [mem_Ioc]
    have := hp.1.2.1.pos
    constructor <;> push_cast <;> omega
  set B : ℕ → Finset ℕ := fun ℓ => {0, N % ℓ}
  have hB : ∀ ℓ, ℓ.Prime → B ℓ ⊆ range ℓ ∧ (B ℓ).card < ℓ := by
    intro ℓ hℓ
    refine ⟨?_, ?_⟩
    · intro b hb
      simp only [B, mem_insert, mem_singleton] at hb
      rw [mem_range]
      rcases hb with rfl | rfl
      · exact hℓ.pos
      · exact Nat.mod_lt _ hℓ.pos
    · rcases hℓ.eq_two_or_odd' with rfl | hodd
      · have : N % 2 = 0 := Nat.even_iff.1 hN
        simp [B, this]
      · have h3 : 3 ≤ ℓ := by
          rcases hodd with ⟨m, hm⟩
          have := hℓ.two_le; omega
        exact (card_insert_le _ _).trans_lt (by rw [card_singleton]; omega)
  have hAB : ∀ ℓ, ℓ.Prime → ℓ ≤ Q → ∀ n ∈ A, (n % (ℓ : ℤ)).toNat ∉ B ℓ := by
    intro ℓ hℓ hℓQ n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hn
    simp only [Pbig, P, mem_filter, mem_range] at hp
    obtain ⟨⟨hpN, hpp, hqp⟩, hQp, hQq⟩ := hp
    simp only [B, mem_insert, mem_singleton]
    rw [← Int.natCast_mod, Int.toNat_natCast]
    rintro (h0 | h1)
    · have := (Nat.prime_dvd_prime_iff_eq hℓ hpp).1 (Nat.dvd_of_mod_eq_zero h0)
      omega
    · have hdvd : ℓ ∣ N - p := by
        apply Nat.dvd_of_mod_eq_zero
        exact Nat.sub_mod_eq_zero_of_mod_eq h1.symm
      have := (Nat.prime_dvd_prime_iff_eq hℓ hqp).1 hdvd
      omega
  have hmont := montgomery_sieve (by omega : 1 ≤ Q) 0 N A hA B hB hAB
  -- the sieve sum from below
  have hN1 : 1 ≤ N := by omega
  have hcop : ∑ q ∈ (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q N), fC q ≤
      ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q := by
    have hsub : (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q N) ⊆
        (Icc 1 Q).filter Squarefree := by
      intro q hq; rw [mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.1⟩
    have hle : ∀ q ∈ (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q N),
        fC q ≤ hW B q := by
      intro q hq
      rw [mem_filter] at hq
      unfold fC hW
      apply Finset.prod_le_prod₀ (fun ℓ hℓ => cW_nonneg (Nat.prime_of_mem_primeFactors hℓ))
      intro ℓ hℓ
      have hℓp := Nat.prime_of_mem_primeFactors hℓ
      have hℓN : ¬ ℓ ∣ N := by
        intro h
        have := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hℓ) h
        rw [hq.2.2.gcd_eq_one] at this
        exact hℓp.one_lt.ne' (Nat.dvd_one.1 this)
      have hℓ3 : 3 ≤ ℓ := by
        rcases hℓp.eq_two_or_odd' with rfl | hodd
        · exact absurd (even_iff_two_dvd.1 hN) hℓN
        · rcases hodd with ⟨m, hm⟩; have := hℓp.two_le; omega
      have hcard : (B ℓ).card = 2 := by
        simp only [B]
        rw [card_pair]
        intro h
        exact hℓN (Nat.dvd_of_mod_eq_zero h.symm)
      rw [hcard]
      push_cast
      exact cW_le_two_div hℓ3
    rw [← sum_congr rfl (fun q _ => rfl)]
    refine (sum_le_sum hle).trans (sum_le_sum_of_subset_of_nonneg hsub ?_)
    intro q _ _
    unfold hW
    refine prod_nonneg fun ℓ hℓ => ?_
    have hℓp := Nat.prime_of_mem_primeFactors hℓ
    have := (hB ℓ hℓp).2
    have : ((B ℓ).card : ℝ) < ℓ := by exact_mod_cast this
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hsplitC := sum_sqf_c_le_coprime hN1 Q
  have htau := sum_tau_le_sum_sqf Q
  have hge := sum_tau_ge Q hQ
  have hφ : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hR : (0 : ℝ) < ((N : ℝ) / N.totient) ^ 2 := by positivity
  -- `log² 4 / 2 > 3/4`
  have hD : 0 < Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4 := by
    have h4 : Real.log 4 ≤ Real.log ((Q : ℝ) + 1) := by
      apply Real.log_le_log (by norm_num)
      have : (3 : ℝ) ≤ Q := by exact_mod_cast hQ
      linarith
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
    nlinarith
  set S := ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q
  have hS : (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4) ≤ ((N : ℝ) / N.totient) ^ 2 * S := by
    have h1 : ∑ q ∈ (Icc 1 Q).filter Squarefree, fC q ≤ ((N : ℝ) / N.totient) ^ 2 * S :=
      hsplitC.trans (mul_le_mul_of_nonneg_left hcop hR.le)
    have h2 : ∑ n ∈ Icc 1 Q, tau n / n ≤ ∑ q ∈ (Icc 1 Q).filter Squarefree, fC q := htau
    linarith
  have hbig : (Pbig.card : ℝ) ≤ (N + 2 * (Q : ℝ) ^ 2) * ((N : ℝ) / N.totient) ^ 2 /
      (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4) := by
    rw [le_div_iff₀ hD, ← hAcard]
    have hm : (A.card : ℝ) * S ≤ N + 2 * (Q : ℝ) ^ 2 := hmont
    calc (A.card : ℝ) * (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4)
        ≤ (A.card : ℝ) * (((N : ℝ) / N.totient) ^ 2 * S) :=
          mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg _)
      _ = ((A.card : ℝ) * S) * ((N : ℝ) / N.totient) ^ 2 := by ring
      _ ≤ (N + 2 * (Q : ℝ) ^ 2) * ((N : ℝ) / N.totient) ^ 2 :=
          mul_le_mul_of_nonneg_right hm hR.le
  rw [hsplit, Nat.cast_add]
  linarith


end

/-! ### copied from PNTPort/LargeSieve/MontgomeryTwin.lean -/
section

/-!
# An explicit upper bound for twin primes from Montgomery's sieve

Lab proof, unit U-5558, CLOUD 20261019T1321Z-cloud25. AI wrote this file. Known mathematics,
Brun 1919 for the order `N/log² N`. No cited input. The twin prime conjecture is open; this is an
upper bound.

* `twin_upper_montgomery`: for `N ≥ 1` and `Q ≥ 3`,
  `#{p ≤ N : p, p + 2 prime} ≤ Q + 4 (N + 2Q²)/(log²(Q + 1)/2 - 3/4)`.
  With `Q` near `√N/log N` this is `(32 + o(1)) N/log² N`, that is `(16/C₂ + o(1)) · 2C₂N/log² N`.

The sieve: modulo a prime `ℓ ≤ Q`, a prime `p > Q` with `p + 2` prime misses the classes `0` and
`-2 mod ℓ`; for `ℓ = 2` these coincide.
-/


open Finset Real

/-- **Twin prime upper bound, explicit, from Montgomery's sieve.** -/
private theorem twin_upper_montgomery (N Q : ℕ) (hN : 1 ≤ N) (hQ : 3 ≤ Q) :
    ((((Icc 1 N).filter (fun p => p.Prime ∧ (p + 2).Prime)).card : ℕ) : ℝ) ≤
      Q + 4 * (N + 2 * (Q : ℝ) ^ 2) / (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4) := by
  set P := (Icc 1 N).filter (fun p => p.Prime ∧ (p + 2).Prime)
  set Pbig := P.filter (fun p => Q < p)
  set Psmall := P.filter (fun p => ¬ Q < p)
  have hsplit : P.card = Pbig.card + Psmall.card := (card_filter_add_card_filter_not _).symm
  have hsmall : (Psmall.card : ℝ) ≤ Q := by
    have hsub : Psmall ⊆ Icc 1 Q := by
      intro p hp
      simp only [Psmall, P, mem_filter, mem_Icc, not_lt] at hp
      exact mem_Icc.2 ⟨hp.1.1.1, hp.2⟩
    have := card_le_card hsub
    rw [Nat.card_Icc] at this
    exact_mod_cast (by omega : Psmall.card ≤ Q)
  set A : Finset ℤ := Pbig.image (fun p : ℕ => (p : ℤ))
  have hAcard : A.card = Pbig.card := card_image_of_injective _ Nat.cast_injective
  have hA : A ⊆ Ioc (0 : ℤ) (0 + (N : ℕ)) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hn
    simp only [Pbig, P, mem_filter, mem_Icc] at hp
    rw [mem_Ioc]
    constructor <;> push_cast <;> omega
  set B : ℕ → Finset ℕ := fun ℓ => {0, (ℓ - 2 % ℓ) % ℓ}
  have hB : ∀ ℓ, ℓ.Prime → B ℓ ⊆ range ℓ ∧ (B ℓ).card < ℓ := by
    intro ℓ hℓ
    refine ⟨?_, ?_⟩
    · intro b hb
      simp only [B, mem_insert, mem_singleton] at hb
      rw [mem_range]
      rcases hb with rfl | rfl
      · exact hℓ.pos
      · exact Nat.mod_lt _ hℓ.pos
    · rcases hℓ.eq_two_or_odd' with rfl | hodd
      · simp [B]
      · have h3 : 3 ≤ ℓ := by
          rcases hodd with ⟨m, hm⟩
          have := hℓ.two_le; omega
        exact (card_insert_le _ _).trans_lt (by rw [card_singleton]; omega)
  have hAB : ∀ ℓ, ℓ.Prime → ℓ ≤ Q → ∀ n ∈ A, (n % (ℓ : ℤ)).toNat ∉ B ℓ := by
    intro ℓ hℓ hℓQ n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hn
    simp only [Pbig, P, mem_filter, mem_Icc] at hp
    obtain ⟨⟨-, hpp, hqp⟩, hQp⟩ := hp
    simp only [B, mem_insert, mem_singleton]
    rw [← Int.natCast_mod, Int.toNat_natCast]
    rintro (h0 | h1)
    · have := (Nat.prime_dvd_prime_iff_eq hℓ hpp).1 (Nat.dvd_of_mod_eq_zero h0)
      omega
    · have hdvd : ℓ ∣ p + 2 := by
        apply Nat.dvd_of_mod_eq_zero
        have h2 : 2 % ℓ ≤ ℓ := (Nat.mod_lt _ hℓ.pos).le
        rw [Nat.add_mod, h1]
        rcases Nat.lt_or_ge (2 % ℓ) 1 with h | h
        · have : 2 % ℓ = 0 := by omega
          rw [this, Nat.sub_zero, Nat.mod_self]; simp
        · rw [Nat.mod_eq_of_lt (by omega : ℓ - 2 % ℓ < ℓ), Nat.sub_add_cancel h2, Nat.mod_self]
      have := (Nat.prime_dvd_prime_iff_eq hℓ hqp).1 hdvd
      omega
  have hmont := montgomery_sieve (by omega : 1 ≤ Q) 0 N A hA B hB hAB
  have hcop : ∑ q ∈ (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q 2), fC q ≤
      ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q := by
    have hsub : (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q 2) ⊆
        (Icc 1 Q).filter Squarefree := by
      intro q hq; rw [mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.1⟩
    have hle : ∀ q ∈ (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q 2),
        fC q ≤ hW B q := by
      intro q hq
      rw [mem_filter] at hq
      unfold fC hW
      apply Finset.prod_le_prod₀ (fun ℓ hℓ => cW_nonneg (Nat.prime_of_mem_primeFactors hℓ))
      intro ℓ hℓ
      have hℓp := Nat.prime_of_mem_primeFactors hℓ
      have hℓ2 : ¬ ℓ ∣ 2 := by
        intro h
        have := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hℓ) h
        rw [hq.2.2.gcd_eq_one] at this
        exact hℓp.one_lt.ne' (Nat.dvd_one.1 this)
      have hℓ3 : 3 ≤ ℓ := by
        rcases hℓp.eq_two_or_odd' with rfl | hodd
        · exact absurd (dvd_refl 2) hℓ2
        · rcases hodd with ⟨m, hm⟩; have := hℓp.two_le; omega
      have hcard : (B ℓ).card = 2 := by
        simp only [B]
        rw [card_pair]
        rw [Nat.mod_eq_of_lt (by omega : 2 < ℓ), Nat.mod_eq_of_lt (by omega : ℓ - 2 < ℓ)]
        omega
      rw [hcard]
      push_cast
      exact cW_le_two_div hℓ3
    refine (sum_le_sum hle).trans (sum_le_sum_of_subset_of_nonneg hsub ?_)
    intro q _ _
    unfold hW
    refine prod_nonneg fun ℓ hℓ => ?_
    have hℓp := Nat.prime_of_mem_primeFactors hℓ
    have := (hB ℓ hℓp).2
    have : ((B ℓ).card : ℝ) < ℓ := by exact_mod_cast this
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hsplitC := sum_sqf_c_le_coprime (by norm_num : 1 ≤ 2) Q
  have h2 : ((2 : ℕ) : ℝ) / (Nat.totient 2 : ℝ) = 2 := by
    rw [Nat.totient_prime Nat.prime_two]; norm_num
  rw [h2] at hsplitC
  have htau : ∑ n ∈ Icc 1 Q, tau n / n ≤ ∑ q ∈ (Icc 1 Q).filter Squarefree, fC q :=
    sum_tau_le_sum_sqf Q
  have hge := sum_tau_ge Q hQ
  have hD : 0 < Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4 := by
    have h4 : Real.log 4 ≤ Real.log ((Q : ℝ) + 1) := by
      apply Real.log_le_log (by norm_num)
      have : (3 : ℝ) ≤ Q := by exact_mod_cast hQ
      linarith
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
    nlinarith
  set S := ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q
  have hS : (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4) ≤ 4 * S := by
    have h1 : ∑ q ∈ (Icc 1 Q).filter Squarefree, fC q ≤ (2 : ℝ) ^ 2 * S :=
      hsplitC.trans (mul_le_mul_of_nonneg_left hcop (by norm_num))
    linarith
  have hbig : (Pbig.card : ℝ) ≤ 4 * (N + 2 * (Q : ℝ) ^ 2) /
      (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4) := by
    rw [le_div_iff₀ hD, ← hAcard]
    have hm : (A.card : ℝ) * S ≤ N + 2 * (Q : ℝ) ^ 2 := hmont
    calc (A.card : ℝ) * (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4)
        ≤ (A.card : ℝ) * (4 * S) := mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg _)
      _ = 4 * ((A.card : ℝ) * S) := by ring
      _ ≤ 4 * (N + 2 * (Q : ℝ) ^ 2) := by linarith
  rw [hsplit, Nat.cast_add]
  linarith


end

section
open Finset Real

/-- **Upper bound for prime pairs with a fixed even difference.** For `d ≥ 2` even and `N ≥ 1`,
`Q ≥ 3`, the number of `p ≤ N` with `p` and `p + d` both prime is at most
`Q + (d/φ(d))² (N + 2Q²) / (log²(Q+1)/2 - 3/4)`. Same Montgomery sieve as
`twin_upper_montgomery`, with the two forbidden classes `0` and `-d` modulo `ℓ`. -/
theorem pair_upper_montgomery (N Q d : ℕ) (hN : 1 ≤ N) (hQ : 3 ≤ Q) (hd : 2 ≤ d)
    (heven : d % 2 = 0) :
    ((((Icc 1 N).filter (fun p => p.Prime ∧ (p + d).Prime)).card : ℕ) : ℝ) ≤
      Q + ((d : ℝ) / d.totient) ^ 2 * (N + 2 * (Q : ℝ) ^ 2) /
        (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4) := by
  set P := (Icc 1 N).filter (fun p => p.Prime ∧ (p + d).Prime)
  set Pbig := P.filter (fun p => Q < p)
  set Psmall := P.filter (fun p => ¬ Q < p)
  have hsplit : P.card = Pbig.card + Psmall.card := (card_filter_add_card_filter_not _).symm
  have hsmall : (Psmall.card : ℝ) ≤ Q := by
    have hsub : Psmall ⊆ Icc 1 Q := by
      intro p hp
      simp only [Psmall, P, mem_filter, mem_Icc, not_lt] at hp
      exact mem_Icc.2 ⟨hp.1.1.1, hp.2⟩
    have := card_le_card hsub
    rw [Nat.card_Icc] at this
    exact_mod_cast (by omega : Psmall.card ≤ Q)
  set A : Finset ℤ := Pbig.image (fun p : ℕ => (p : ℤ))
  have hAcard : A.card = Pbig.card := card_image_of_injective _ Nat.cast_injective
  have hA : A ⊆ Ioc (0 : ℤ) (0 + (N : ℕ)) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hn
    simp only [Pbig, P, mem_filter, mem_Icc] at hp
    rw [mem_Ioc]
    constructor <;> push_cast <;> omega
  set B : ℕ → Finset ℕ := fun ℓ => {0, (ℓ - d % ℓ) % ℓ}
  have hB : ∀ ℓ, ℓ.Prime → B ℓ ⊆ range ℓ ∧ (B ℓ).card < ℓ := by
    intro ℓ hℓ
    refine ⟨?_, ?_⟩
    · intro b hb
      simp only [B, mem_insert, mem_singleton] at hb
      rw [mem_range]
      rcases hb with rfl | rfl
      · exact hℓ.pos
      · exact Nat.mod_lt _ hℓ.pos
    · rcases hℓ.eq_two_or_odd' with rfl | hodd
      · have h2 : d % 2 = 0 := heven
        simp only [B, h2, Nat.sub_zero, Nat.mod_self]
        norm_num
      · have h3 : 3 ≤ ℓ := by
          rcases hodd with ⟨m, hm⟩
          have := hℓ.two_le; omega
        exact (card_insert_le _ _).trans_lt (by rw [card_singleton]; omega)
  have hAB : ∀ ℓ, ℓ.Prime → ℓ ≤ Q → ∀ n ∈ A, (n % (ℓ : ℤ)).toNat ∉ B ℓ := by
    intro ℓ hℓ hℓQ n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hn
    simp only [Pbig, P, mem_filter, mem_Icc] at hp
    obtain ⟨⟨-, hpp, hqp⟩, hQp⟩ := hp
    simp only [B, mem_insert, mem_singleton]
    rw [← Int.natCast_mod, Int.toNat_natCast]
    rintro (h0 | h1)
    · have := (Nat.prime_dvd_prime_iff_eq hℓ hpp).1 (Nat.dvd_of_mod_eq_zero h0)
      omega
    · have hdm : d % ℓ < ℓ := Nat.mod_lt _ hℓ.pos
      have hdvd : ℓ ∣ p + d := by
        apply Nat.dvd_of_mod_eq_zero
        rw [Nat.add_mod, h1]
        rcases Nat.eq_zero_or_pos (d % ℓ) with h | h
        · rw [h]; simp
        · rw [Nat.mod_eq_of_lt (by omega : ℓ - d % ℓ < ℓ), Nat.sub_add_cancel hdm.le, Nat.mod_self]
      have := (Nat.prime_dvd_prime_iff_eq hℓ hqp).1 hdvd
      omega
  have hmont := montgomery_sieve (by omega : 1 ≤ Q) 0 N A hA B hB hAB
  have hcop : ∑ q ∈ (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q d), fC q ≤
      ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q := by
    have hsub : (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q d) ⊆
        (Icc 1 Q).filter Squarefree := by
      intro q hq; rw [mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.1⟩
    have hle : ∀ q ∈ (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q d),
        fC q ≤ hW B q := by
      intro q hq
      rw [mem_filter] at hq
      unfold fC hW
      apply Finset.prod_le_prod₀ (fun ℓ hℓ => cW_nonneg (Nat.prime_of_mem_primeFactors hℓ))
      intro ℓ hℓ
      have hℓp := Nat.prime_of_mem_primeFactors hℓ
      have hℓ2 : ¬ ℓ ∣ d := by
        intro h
        have := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hℓ) h
        rw [hq.2.2.gcd_eq_one] at this
        exact hℓp.one_lt.ne' (Nat.dvd_one.1 this)
      have hℓ3 : 3 ≤ ℓ := by
        rcases hℓp.eq_two_or_odd' with rfl | hodd
        · exact absurd (Nat.dvd_of_mod_eq_zero heven) hℓ2
        · rcases hodd with ⟨m, hm⟩; have := hℓp.two_le; omega
      have hcard : (B ℓ).card = 2 := by
        have hpos : 0 < d % ℓ := by
          rcases Nat.eq_zero_or_pos (d % ℓ) with h | h
          · exact absurd (Nat.dvd_of_mod_eq_zero h) hℓ2
          · exact h
        have hlt : d % ℓ < ℓ := Nat.mod_lt _ hℓp.pos
        have hmod : (ℓ - d % ℓ) % ℓ = ℓ - d % ℓ := Nat.mod_eq_of_lt (by omega)
        have hBeq : B ℓ = {0, ℓ - d % ℓ} := by simp only [B, hmod]
        rw [hBeq, card_pair]
        omega
      rw [hcard]
      push_cast
      exact cW_le_two_div hℓ3
    refine (sum_le_sum hle).trans (sum_le_sum_of_subset_of_nonneg hsub ?_)
    intro q _ _
    unfold hW
    refine prod_nonneg fun ℓ hℓ => ?_
    have hℓp := Nat.prime_of_mem_primeFactors hℓ
    have := (hB ℓ hℓp).2
    have : ((B ℓ).card : ℝ) < ℓ := by exact_mod_cast this
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hsplitC := sum_sqf_c_le_coprime (k := d) (by omega : 1 ≤ d) Q
  have hφ : (0 : ℝ) < d.totient := by
    have : 0 < d := by omega
    exact_mod_cast Nat.totient_pos.2 this
  have hR : (0 : ℝ) ≤ ((d : ℝ) / d.totient) ^ 2 := by positivity
  have hD : 0 < Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4 := by
    have h4 : Real.log 4 ≤ Real.log ((Q : ℝ) + 1) := by
      apply Real.log_le_log (by norm_num)
      have : (3 : ℝ) ≤ Q := by exact_mod_cast hQ
      linarith
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
    nlinarith
  set S := ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q
  have hS : (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4) ≤ ((d : ℝ) / d.totient) ^ 2 * S := by
    have h1 : ∑ q ∈ (Icc 1 Q).filter Squarefree, fC q ≤ ((d : ℝ) / d.totient) ^ 2 * S :=
      hsplitC.trans (mul_le_mul_of_nonneg_left hcop hR)
    have h2 : ∑ n ∈ Icc 1 Q, tau n / n ≤ ∑ q ∈ (Icc 1 Q).filter Squarefree, fC q :=
      sum_tau_le_sum_sqf Q
    have h3 := sum_tau_ge Q hQ
    linarith
  have hbig : (Pbig.card : ℝ) ≤ ((d : ℝ) / d.totient) ^ 2 * (N + 2 * (Q : ℝ) ^ 2) /
      (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4) := by
    rw [le_div_iff₀ hD, ← hAcard]
    have hm : (A.card : ℝ) * S ≤ N + 2 * (Q : ℝ) ^ 2 := hmont
    calc (A.card : ℝ) * (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4)
        ≤ (A.card : ℝ) * (((d : ℝ) / d.totient) ^ 2 * S) :=
          mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg _)
      _ = ((A.card : ℝ) * S) * ((d : ℝ) / d.totient) ^ 2 := by ring
      _ ≤ (N + 2 * (Q : ℝ) ^ 2) * ((d : ℝ) / d.totient) ^ 2 :=
          mul_le_mul_of_nonneg_right hm hR
      _ = ((d : ℝ) / d.totient) ^ 2 * (N + 2 * (Q : ℝ) ^ 2) := by ring
  rw [hsplit, Nat.cast_add]
  linarith
end

end LeanLab.PNTPort.LargeSieve

namespace LeanLab.OpenProblems
open Erdos9 Lemoine Erdos17
open Finset

section


/-- `log t ≤ 4 t^(1/4)` for `t > 0`, from `log y ≤ y - 1`. -/
private lemma log_le_four_rpow (t : ℝ) (ht : 0 < t) : Real.log t ≤ 4 * t ^ (1 / 4 : ℝ) := by
  have h1 : Real.log t = 4 * Real.log (t ^ (1 / 4 : ℝ)) := by
    rw [Real.log_rpow ht]
    ring
  have h3 : (0 : ℝ) < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have h2 : Real.log (t ^ (1 / 4 : ℝ)) ≤ t ^ (1 / 4 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos h3
  rw [h1]
  linarith

/-- `(log t)² ≤ 16 √t` for `t ≥ 1`. -/
private lemma log_sq_le_sixteen_sqrt (t : ℝ) (ht : 1 ≤ t) :
    Real.log t ^ 2 ≤ 16 * Real.sqrt t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have h := log_le_four_rpow t ht0
  have hsq : Real.log t ^ 2 ≤ (4 * t ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ hlog0 h 2
  have hrw : (4 * t ^ (1 / 4 : ℝ)) ^ 2 = 16 * Real.sqrt t := by
    have h2 : (t ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt t := by
      rw [pow_two, ← Real.rpow_add ht0, Real.sqrt_eq_rpow]
      norm_num
    rw [mul_pow, h2]
    ring
  linarith

/-- A crude lower bound `2.07 ≤ log 10`, from `log 8 = 3 log 2 ≤ log 10`. -/
private lemma log_ten_ge : (2.07 : ℝ) ≤ Real.log 10 := by
  have h8 : Real.log 8 ≤ Real.log 10 := Real.log_le_log (by norm_num) (by norm_num)
  have h82 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast
    ring
  have h2 := Real.log_two_gt_d9
  linarith

/-- The number of cluster primes up to `x` is at most `10^6 x / (log x)²`. From
`prime_near_of_cluster` each cluster prime `p > 9` has `p - 2`, `p - 4` or `p - 6` prime, and
Montgomery's sieve bounds the number of prime pairs with a fixed difference. -/
private theorem cluster_ncard_le (x : ℕ) (hx : 3 ≤ x) :
    ((({p : ℕ | IsClusterPrime p} ∩ Set.Iic x).ncard : ℕ) : ℝ) ≤
      10 ^ 6 * x / Real.log x ^ 2 := by
  classical
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hlog2pos : (0 : ℝ) < Real.log x ^ 2 := by positivity
  have hlogsq : Real.log x ^ 2 ≤ 16 * Real.sqrt x := log_sq_le_sixteen_sqrt x hx1
  set T : Finset ℕ := (Icc 1 x).filter (fun p => IsClusterPrime p) with hTdef
  have hTeq : ({p : ℕ | IsClusterPrime p} ∩ Set.Iic x) = (T : Set ℕ) := by
    ext p
    rw [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iic, hTdef]
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hc, hpx⟩
      exact ⟨⟨by have := hc.1.two_le; omega, hpx⟩, hc⟩
    · rintro ⟨⟨-, hpx⟩, hc⟩
      exact ⟨hc, hpx⟩
  rw [hTeq, Set.ncard_coe_finset]
  by_cases hsmall : x ≤ 10 ^ 8
  · -- small `x`: count everything
    have hcard : T.card ≤ x := by
      calc T.card ≤ (Icc 1 x).card := card_le_card (filter_subset _ _)
        _ = x := by rw [Nat.card_Icc]; omega
    have hsqrt_le : Real.sqrt x ≤ 10 ^ 4 := by
      have h1 : Real.sqrt x ^ 2 = (x : ℝ) := Real.sq_sqrt hx0.le
      have h2 : (x : ℝ) ≤ 10 ^ 8 := by exact_mod_cast hsmall
      nlinarith [Real.sqrt_nonneg x]
    have h1 : ((T.card : ℕ) : ℝ) ≤ (x : ℝ) + 1 := by
      have : ((T.card : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hcard
      linarith only [this, hx0.le]
    have h2 : ((x : ℝ) + 1) ≤ 10 ^ 6 * x / Real.log x ^ 2 := by
      rw [le_div_iff₀ hlog2pos]
      have h3 : ((x : ℝ) + 1) * Real.log x ^ 2 ≤ ((x : ℝ) + 1) * (16 * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hlogsq (by linarith only [hx0.le])
      nlinarith only [h3, hsqrt_le, hx1]
    exact le_trans h1 h2
  · -- large `x`: sieve the three shifts
    have hbig : 10 ^ 8 < x := not_le.mp hsmall
    have hx8 : (10 ^ 8 : ℝ) < (x : ℝ) := by exact_mod_cast hbig
    have hlog8 : (8 : ℝ) ≤ Real.log x := by
      have hxge : (10 ^ 8 : ℝ) ≤ (x : ℝ) := le_of_lt hx8
      have h1 : Real.log (10 ^ 8 : ℝ) ≤ Real.log x := Real.log_le_log (by norm_num) hxge
      have h2 : Real.log (10 ^ 8 : ℝ) = 8 * Real.log 10 := by
        rw [show (10 ^ 8 : ℝ) = (10 : ℝ) ^ 8 by norm_num, Real.log_pow]
        push_cast
        ring
      have h3 := log_ten_ge
      linarith
    set Q := Nat.sqrt x with hQdef
    have hQ3 : 3 ≤ Q := by
      rw [hQdef]
      have h9 : 3 ^ 2 ≤ x := by
        have : (3 : ℕ) ^ 2 = 9 := by norm_num
        omega
      exact Nat.le_sqrt.mpr h9
    have hQsq : (Q : ℝ) ^ 2 ≤ (x : ℝ) := by
      have h := Nat.sqrt_le' x
      have h2 : ((Q ^ 2 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast h
      calc (Q : ℝ) ^ 2 = ((Q ^ 2 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (x : ℝ) := h2
    have hQup : (x : ℝ) < ((Q : ℝ) + 1) ^ 2 := by
      have h := Nat.lt_succ_sqrt x
      have h' : x < (Q + 1) ^ 2 := by
        rw [pow_two]
        simpa using h
      have h2 : ((x : ℕ) : ℝ) < ((((Q + 1) ^ 2 : ℕ)) : ℝ) := by exact_mod_cast h'
      calc (x : ℝ) < ((((Q + 1) ^ 2 : ℕ)) : ℝ) := h2
        _ = ((Q : ℝ) + 1) ^ 2 := by push_cast; ring
    have hlogQ : Real.log x ≤ 2 * Real.log ((Q : ℝ) + 1) := by
      have h0 : Real.log x ≤ Real.log (((Q : ℝ) + 1) ^ 2) := Real.log_le_log hx0 hQup.le
      have h1 : Real.log (((Q : ℝ) + 1) ^ 2) = 2 * Real.log ((Q : ℝ) + 1) := by
        rw [Real.log_pow]
        push_cast
        ring
      linarith
    set D := Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4 with hDdef
    have hDpos : 0 < D := by
      have h4 : Real.log 4 ≤ Real.log ((Q : ℝ) + 1) := by
        apply Real.log_le_log (by norm_num)
        have : (3 : ℝ) ≤ Q := by exact_mod_cast hQ3
        linarith
      have hl4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        ring
      have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
      simp only [hDdef]
      nlinarith
    have hDge : Real.log x ^ 2 / 16 ≤ D := by
      have hb4 : (4 : ℝ) ≤ Real.log ((Q : ℝ) + 1) := by linarith
      have hsq2 := pow_le_pow_left₀ hlogpos.le hlogQ 2
      have h4 : (2 * Real.log ((Q : ℝ) + 1)) ^ 2 = 4 * Real.log ((Q : ℝ) + 1) ^ 2 := by ring
      have ha : Real.log x ^ 2 ≤ 4 * Real.log ((Q : ℝ) + 1) ^ 2 := by
        linarith only [hsq2, h4]
      have hb0 : (0 : ℝ) ≤ Real.log ((Q : ℝ) + 1) := by linarith
      have hb : 12 ≤ 4 * Real.log ((Q : ℝ) + 1) ^ 2 := by nlinarith
      simp only [hDdef]
      nlinarith
    set A : ℕ → Finset ℕ := fun d => (Icc 1 x).filter (fun p => p.Prime ∧ (p + d).Prime)
      with hAdef
    have hpair : ∀ d ∈ ({2, 4, 6} : Finset ℕ),
        ((A d).card : ℝ) ≤ Q + 432 * ((x : ℝ) / Real.log x ^ 2) := by
      intro d hd
      have hcases : d = 2 ∨ d = 4 ∨ d = 6 := by
        simpa using hd
      have hd2 : 2 ≤ d := by rcases hcases with rfl | rfl | rfl <;> norm_num
      have hde : d % 2 = 0 := by rcases hcases with rfl | rfl | rfl <;> norm_num
      have htot : ((d : ℝ) / d.totient) ^ 2 ≤ 9 := by
        rcases hcases with rfl | rfl | rfl
        · have h2 : Nat.totient 2 = 1 := by decide
          rw [h2]; norm_num
        · have h4 : Nat.totient 4 = 2 := by decide
          rw [h4]; norm_num
        · have h6 : Nat.totient 6 = 2 := by decide
          rw [h6]; norm_num
      have hb := LeanLab.PNTPort.LargeSieve.pair_upper_montgomery x Q d (by omega) hQ3 hd2 hde
      rw [hAdef]
      set Afin := (Icc 1 x).filter (fun p => p.Prime ∧ (p + d).Prime) with hAfin
      have hxQ : (x : ℝ) + 2 * (Q : ℝ) ^ 2 ≤ 3 * x := by nlinarith [hQsq]
      have hnum : ((d : ℝ) / d.totient) ^ 2 * ((x : ℝ) + 2 * (Q : ℝ) ^ 2) ≤ 27 * x := by
        have h0 : (0 : ℝ) ≤ ((d : ℝ) / d.totient) ^ 2 := by positivity
        have h1 : ((d : ℝ) / d.totient) ^ 2 * ((x : ℝ) + 2 * (Q : ℝ) ^ 2) ≤ 9 * (3 * x) := by
          apply mul_le_mul htot hxQ (by positivity) (by positivity)
        linarith
      have step1 : ((d : ℝ) / d.totient) ^ 2 * ((x : ℝ) + 2 * (Q : ℝ) ^ 2) / D ≤ 27 * x / D := by
        rw [div_le_div_iff_of_pos_right hDpos]
        exact hnum
      have step2 : 27 * (x : ℝ) / D ≤ 432 * ((x : ℝ) / Real.log x ^ 2) := by
        have h2 : 27 * (x : ℝ) / D ≤ 432 * (x : ℝ) / Real.log x ^ 2 := by
          rw [div_le_div_iff₀ hDpos hlog2pos]
          nlinarith only [hDge, hx0.le]
        simpa only [mul_div_assoc] using h2
      linarith only [hb, step1, step2]
    have hcard9 : (T.filter (fun p => ¬ 9 < p)).card ≤ 9 := by
      have hsub : T.filter (fun p => ¬ 9 < p) ⊆ Icc 1 9 := by
        intro p hp
        simp only [mem_filter, hTdef, mem_Icc] at hp
        exact mem_Icc.2 ⟨hp.1.1.1, by omega⟩
      have := card_le_card hsub
      rw [Nat.card_Icc] at this
      omega
    have hS2 : (T.filter (fun p => (p - 2).Prime)).card ≤ (A 2).card := by
      have hsub : T.filter (fun p => (p - 2).Prime) ⊆ (A 2).image (fun m => m + 2) := by
        intro p hp
        simp only [mem_filter, hTdef, mem_Icc] at hp
        obtain ⟨⟨⟨hp1, hpx⟩, hc⟩, hpr⟩ := hp
        have hp2 : 2 ≤ p := by have := hpr.two_le; omega
        refine mem_image.2 ⟨p - 2, ?_, by omega⟩
        simp only [hAdef, mem_filter, mem_Icc]
        exact ⟨⟨by have := hpr.two_le; omega, by omega⟩, hpr,
          by rw [Nat.sub_add_cancel hp2]; exact hc.1⟩
      calc _ ≤ ((A 2).image (fun m => m + 2)).card := card_le_card hsub
        _ = (A 2).card := card_image_of_injective _ (fun a b h => by omega)
    have hS4 : (T.filter (fun p => (p - 4).Prime)).card ≤ (A 4).card := by
      have hsub : T.filter (fun p => (p - 4).Prime) ⊆ (A 4).image (fun m => m + 4) := by
        intro p hp
        simp only [mem_filter, hTdef, mem_Icc] at hp
        obtain ⟨⟨⟨hp1, hpx⟩, hc⟩, hpr⟩ := hp
        have hp2 : 4 ≤ p := by have := hpr.two_le; omega
        refine mem_image.2 ⟨p - 4, ?_, by omega⟩
        simp only [hAdef, mem_filter, mem_Icc]
        exact ⟨⟨by have := hpr.two_le; omega, by omega⟩, hpr,
          by rw [Nat.sub_add_cancel hp2]; exact hc.1⟩
      calc _ ≤ ((A 4).image (fun m => m + 4)).card := card_le_card hsub
        _ = (A 4).card := card_image_of_injective _ (fun a b h => by omega)
    have hS6 : (T.filter (fun p => (p - 6).Prime)).card ≤ (A 6).card := by
      have hsub : T.filter (fun p => (p - 6).Prime) ⊆ (A 6).image (fun m => m + 6) := by
        intro p hp
        simp only [mem_filter, hTdef, mem_Icc] at hp
        obtain ⟨⟨⟨hp1, hpx⟩, hc⟩, hpr⟩ := hp
        have hp2 : 6 ≤ p := by have := hpr.two_le; omega
        refine mem_image.2 ⟨p - 6, ?_, by omega⟩
        simp only [hAdef, mem_filter, mem_Icc]
        exact ⟨⟨by have := hpr.two_le; omega, by omega⟩, hpr,
          by rw [Nat.sub_add_cancel hp2]; exact hc.1⟩
      calc _ ≤ ((A 6).image (fun m => m + 6)).card := card_le_card hsub
        _ = (A 6).card := card_image_of_injective _ (fun a b h => by omega)
    have hchain : T.card ≤ 9 + (A 2).card + (A 4).card + (A 6).card := by
      have hsplit : T.card = (T.filter (fun p => 9 < p)).card +
          (T.filter (fun p => ¬ 9 < p)).card := (card_filter_add_card_filter_not _).symm
      have hsub : T.filter (fun p => 9 < p) ⊆
          (T.filter (fun p => (p - 2).Prime) ∪ T.filter (fun p => (p - 4).Prime)) ∪
            T.filter (fun p => (p - 6).Prime) := by
        intro p hp
        simp only [mem_filter, hTdef, mem_Icc] at hp
        obtain ⟨⟨⟨hp1, hpx⟩, hc⟩, h9⟩ := hp
        have hpT : p ∈ T := by
          rw [hTdef]
          exact mem_filter.2 ⟨mem_Icc.2 ⟨hp1, hpx⟩, hc⟩
        have hodd : Odd p := hc.1.odd_of_ne_two (by omega)
        rcases prime_near_of_cluster hc hodd h9 with h2 | h4 | h6
        · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hpT, h2⟩))
        · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hpT, h4⟩))
        · exact mem_union_right _ (mem_filter.2 ⟨hpT, h6⟩)
      have h1 : (T.filter (fun p => 9 < p)).card ≤
          (T.filter (fun p => (p - 2).Prime) ∪ T.filter (fun p => (p - 4).Prime)).card +
            (T.filter (fun p => (p - 6).Prime)).card :=
        (card_le_card hsub).trans (card_union_le _ _)
      have h2 : (T.filter (fun p => (p - 2).Prime) ∪
            T.filter (fun p => (p - 4).Prime)).card ≤
          (T.filter (fun p => (p - 2).Prime)).card +
            (T.filter (fun p => (p - 4).Prime)).card := card_union_le _ _
      omega
    have hchainR : ((T.card : ℕ) : ℝ) ≤ 9 + ((A 2).card : ℝ) + ((A 4).card : ℝ) + ((A 6).card : ℝ) := by
      have h := hchain
      push_cast
      exact_mod_cast h
    have hp2 := hpair 2 (by norm_num)
    have hp4 := hpair 4 (by norm_num)
    have hp6 := hpair 6 (by norm_num)
    have hQle : (Q : ℝ) ≤ Real.sqrt x := by
      have h1 : Real.sqrt x ^ 2 = (x : ℝ) := Real.sq_sqrt hx0.le
      nlinarith [Real.sqrt_nonneg x]
    have hs3 : (3 : ℝ) ≤ Real.sqrt x := by
      nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x]
    have hsqx : Real.sqrt x * Real.sqrt x = (x : ℝ) := Real.mul_self_sqrt hx0.le
    have hL : (0 : ℝ) ≤ Real.log x ^ 2 := by positivity
    have hmul : ((9 : ℝ) + 3 * (Q : ℝ)) * Real.log x ^ 2 ≤ 96 * x := by
      have h1 : ((9 : ℝ) + 3 * (Q : ℝ)) * Real.log x ^ 2 ≤
          ((9 : ℝ) + 3 * Real.sqrt x) * Real.log x ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hL
        linarith only [hQle]
      have h2 : ((9 : ℝ) + 3 * Real.sqrt x) * Real.log x ^ 2 ≤
          ((9 : ℝ) + 3 * Real.sqrt x) * (16 * Real.sqrt x) := by
        apply mul_le_mul_of_nonneg_left hlogsq
        linarith only [Real.sqrt_nonneg x]
      have h3 : ((9 : ℝ) + 3 * Real.sqrt x) * (16 * Real.sqrt x) ≤ 96 * x := by
        nlinarith only [hsqx, hs3]
      linarith only [h1, h2, h3]
    have h9Q : (9 : ℝ) + 3 * (Q : ℝ) ≤ 96 * ((x : ℝ) / Real.log x ^ 2) := by
      have h1 : (9 : ℝ) + 3 * (Q : ℝ) ≤ 96 * (x : ℝ) / Real.log x ^ 2 := by
        rw [le_div_iff₀ hlog2pos]
        exact hmul
      simpa only [mul_div_assoc] using h1
    have hxL : (0 : ℝ) ≤ (x : ℝ) / Real.log x ^ 2 := by positivity
    have hfin : 9 + 3 * (Q : ℝ) + 1296 * ((x : ℝ) / Real.log x ^ 2) ≤
        10 ^ 6 * ((x : ℝ) / Real.log x ^ 2) := by
      nlinarith only [h9Q, hxL]
    have hsum : ((A 2).card : ℝ) + ((A 4).card : ℝ) + ((A 6).card : ℝ) ≤
        3 * (Q : ℝ) + 1296 * ((x : ℝ) / Real.log x ^ 2) := by
      linarith only [hp2, hp4, hp6]
    have hsum2 : ((T.card : ℕ) : ℝ) ≤ 9 + 3 * (Q : ℝ) + 1296 * ((x : ℝ) / Real.log x ^ 2) := by
      linarith only [hchainR, hsum]
    simpa only [mul_div_assoc] using le_trans hsum2 hfin

end

/-- Unit U-1603, route lemma, OPEN in the lab. Plain math: at most `C x / (log x)^2` cluster primes
lie below `x`, from `prime_near_of_cluster` and a sieve bound for prime pairs with a fixed even
difference, as in the lab's `BrunGap`. Weaker than the Blecksmith, Erdős and Selfridge bound on the
Erdős 17 page, and it points away from infinitely many, so it bounds the problem, not solves it. -/
theorem route_cluster_count_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 3 ≤ x →
      (({p : ℕ | IsClusterPrime p} ∩ Set.Iic x).ncard : ℝ) ≤ C * x / Real.log x ^ 2 :=
  ⟨10 ^ 6, by norm_num, fun x hx => cluster_ncard_le x hx⟩

end LeanLab.OpenProblems

#print axioms LeanLab.OpenProblems.route_erdos9A_infinite
#print axioms LeanLab.OpenProblems.route_lemoine_positive_density
#print axioms LeanLab.OpenProblems.route_cluster_count_le

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

/-- Unit U-1603, route lemma, OPEN in the lab. Plain math: at most `C x / (log x)^2` cluster primes
lie below `x`, from `prime_near_of_cluster` and a sieve bound for prime pairs with a fixed even
difference, as in the lab's `BrunGap`. Weaker than the Blecksmith, Erdős and Selfridge bound on the
Erdős 17 page, and it points away from infinitely many, so it bounds the problem, not solves it. -/
theorem route_cluster_count_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 3 ≤ x →
      (({p : ℕ | IsClusterPrime p} ∩ Set.Iic x).ncard : ℝ) ≤ C * x / Real.log x ^ 2 := by
  sorry

end LeanLab.OpenProblems

#print axioms LeanLab.OpenProblems.route_erdos9A_infinite
#print axioms LeanLab.OpenProblems.route_lemoine_positive_density
#print axioms LeanLab.OpenProblems.route_cluster_count_le

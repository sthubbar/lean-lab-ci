/-
Split of the fourth fixed candidate batch of row 10^90.
The batch qs.drop 192 carries 17 candidates. It is cut here into four
consecutive sub-batches of 4, 4, 4 and 5 entries. Each sub-batch is one
LEAF; the assembly is only list bookkeeping over the cuts.
The batch is inhabited: batch_members places 10 ^ 90 - 21317 in qs.drop 192.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp395a

namespace LeanLab.DtRS1998.Decomp395a

open Decomp372a

set_option maxRecDepth 100000

/-- The fourth batch of the fixed candidate list has 17 entries, so the cut
4 + 4 + 4 + 5 covers it with no entry left over. This is the fourth conjunct of
batch_lengths, restated under a name for the bookkeeping below. -/
private theorem batch3_card : (qs.drop 192).length = 17 := batch_lengths.2.2.2

/-- The four cuts are nonempty: their lengths are 4, 4, 4 and 5. This records
that none of the four leaves below is a statement about an empty list. -/
private theorem batch3_cut_cards :
    ((qs.drop 192).take 4).length = 4 ∧
    (((qs.drop 192).drop 4).take 4).length = 4 ∧
    (((qs.drop 192).drop 8).take 4).length = 4 ∧
    ((qs.drop 192).drop 12).length = 5 := by
  have h : (qs.drop 192).length = 17 := batch3_card
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.length_take, h]; decide
  · rw [List.length_take, List.length_drop, h]; decide
  · rw [List.length_take, List.length_drop, h]; decide
  · rw [List.length_drop, h]


open LeanLab.Verifications.Pratt

private theorem pm_cast_dvd (fuel a e p q : ℕ) (hq : q ∣ p) (he : e < 2 ^ fuel) :
    ((pm fuel a e p : ℕ) : ZMod q) = (a : ZMod q) ^ e := by
  have h := congrArg (ZMod.castHom hq (ZMod q)) (pm_cast fuel a e p he)
  simp only [map_pow, map_natCast] at h
  exact h

private theorem dvd_of_order (o n F : ℕ) (hn : n ≠ 0) (hon : o ∣ n) (hF : F ∣ n)
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

private theorem pock_aux (p a Fu : ℕ) (L : List (ℕ × ℕ)) (hp2 : 2 ≤ p) (hp : p < 2 ^ Fu)
    (hFd : (p - 1) % (L.map fun x => x.1 ^ x.2).prod = 0)
    (hbig : p < ((L.map fun x => x.1 ^ x.2).prod + 1) ^ 2)
    (hprimes : ∀ x ∈ L, x.1.Prime)
    (hpow : pm Fu a (p - 1) p = 1 % p)
    (hg : ∀ x ∈ L, Nat.gcd ((pm Fu a ((p - 1) / x.1) p + p - 1) % p) p = 1) : p.Prime := by
  set F := (L.map fun x => x.1 ^ x.2).prod with hFl
  have hn : p - 1 ≠ 0 := by omega
  have hFn : F ∣ p - 1 := Nat.dvd_of_mod_eq_zero hFd
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
  have hpp : (F + 1) ^ 2 ≤ p.minFac ^ 2 := Nat.pow_le_pow_left hle 2
  omega

private theorem pch_0 : (262914779 : ℕ).Prime := by
  refine pock_aux 262914779 2 28 [(28759, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_1 : (44858738278702083458431 : ℕ).Prime := by
  refine pock_aux 44858738278702083458431 2 76 [(262914779, 1), (4521821, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_0
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_2 : (222208712357 : ℕ).Prime := by
  refine pock_aux 222208712357 2 38 [(6340849, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_3 : (1333252274143 : ℕ).Prime := by
  refine pock_aux 1333252274143 2 41 [(222208712357, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_2
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_4 : (87994650093439 : ℕ).Prime := by
  refine pock_aux 87994650093439 2 47 [(1333252274143, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_3
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_5 : (238711006826980384811 : ℕ).Prime := by
  refine pock_aux 238711006826980384811 2 68 [(87994650093439, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_4
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_6 : (29282734270768903962891010511897415388858013301370704349849 : ℕ).Prime := by
  refine pock_aux 29282734270768903962891010511897415388858013301370704349849 2 195 [(44858738278702083458431, 1), (238711006826980384811, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_1
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_5
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_7 : (138735134618068249940585314790630819304626177166999848804790898313621 : ℕ).Prime := by
  refine pock_aux 138735134618068249940585314790630819304626177166999848804790898313621 2 227 [(29282734270768903962891010511897415388858013301370704349849, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_6
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_8 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999978683 : ℕ).Prime := by
  refine pock_aux 999999999999999999999999999999999999999999999999999999999999999999999999999999999999978683 2 299 [(138735134618068249940585314790630819304626177166999848804790898313621, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_7
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_9 : (57577189 : ℕ).Prime := by
  refine pock_aux 57577189 3 26 [(227, 1), (23, 1), (3, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_10 : (1727315671 : ℕ).Prime := by
  refine pock_aux 1727315671 2 31 [(57577189, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_9
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_11 : (10363894027 : ℕ).Prime := by
  refine pock_aux 10363894027 2 34 [(1727315671, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_10
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_12 : (1028672518904914678787 : ℕ).Prime := by
  refine pock_aux 1028672518904914678787 2 70 [(10363894027, 1), (741077, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_11
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_13 : (242766714461559864193733 : ℕ).Prime := by
  refine pock_aux 242766714461559864193733 2 78 [(1028672518904914678787, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_12
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_14 : (6008476182923606638794891751 : ℕ).Prime := by
  refine pock_aux 6008476182923606638794891751 2 93 [(242766714461559864193733, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_13
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_15 : (9587290443432507810251573294497711103 : ℕ).Prime := by
  refine pock_aux 9587290443432507810251573294497711103 2 123 [(6008476182923606638794891751, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_14
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_16 : (16862541642310338767555174552054770421630221333666218858754969901533 : ℕ).Prime := by
  refine pock_aux 16862541642310338767555174552054770421630221333666218858754969901533 2 224 [(9587290443432507810251573294497711103, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_15
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_17 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999979073 : ℕ).Prime := by
  refine pock_aux 999999999999999999999999999999999999999999999999999999999999999999999999999999999999979073 2 299 [(16862541642310338767555174552054770421630221333666218858754969901533, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_16
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_18 : (35423203 : ℕ).Prime := by
  refine pock_aux 35423203 2 26 [(5903867, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_19 : (4465661509399 : ℕ).Prime := by
  refine pock_aux 4465661509399 2 43 [(35423203, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_18
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_20 : (425139907017803599 : ℕ).Prime := by
  refine pock_aux 425139907017803599 2 59 [(4465661509399, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_19
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_21 : (23166168291400451693101258681 : ℕ).Prime := by
  refine pock_aux 23166168291400451693101258681 2 95 [(425139907017803599, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_20
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_22 : (75402680857284256998710949032957023 : ℕ).Prime := by
  refine pock_aux 75402680857284256998710949032957023 2 116 [(23166168291400451693101258681, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_21
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_23 : (27637484300568837707 : ℕ).Prime := by
  refine pock_aux 27637484300568837707 2 65 [(447983, 1), (110569, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_24 : (9803921568627450980392156862745098039215686274509803921568627450980392156862745098039011 : ℕ).Prime := by
  refine pock_aux 9803921568627450980392156862745098039215686274509803921568627450980392156862745098039011 2 293 [(75402680857284256998710949032957023, 1), (27637484300568837707, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_22
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_23
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_25 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999979123 : ℕ).Prime := by
  refine pock_aux 999999999999999999999999999999999999999999999999999999999999999999999999999999999999979123 2 299 [(9803921568627450980392156862745098039215686274509803921568627450980392156862745098039011, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_24
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_26 : (891992009413 : ℕ).Prime := by
  refine pock_aux 891992009413 2 40 [(635599, 1), (5569, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_27 : (28615258868578677863 : ℕ).Prime := by
  refine pock_aux 28615258868578677863 2 65 [(891992009413, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_26
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_28 : (187902721 : ℕ).Prime := by
  refine pock_aux 187902721 3 28 [(5437, 1), (5, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_29 : (1210522618274796991980478764186600689888293 : ℕ).Prime := by
  refine pock_aux 1210522618274796991980478764186600689888293 2 140 [(28615258868578677863, 1), (187902721, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_27
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_28
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_30 : (360533650597 : ℕ).Prime := by
  refine pock_aux 360533650597 2 39 [(242257, 1), (2531, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_31 : (513783444221420620363397 : ℕ).Prime := by
  refine pock_aux 513783444221420620363397 2 79 [(360533650597, 1), (39877, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_30
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_32 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999979159 : ℕ).Prime := by
  refine pock_aux 999999999999999999999999999999999999999999999999999999999999999999999999999999999999979159 2 299 [(1210522618274796991980478764186600689888293, 1), (513783444221420620363397, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_29
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_31
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_33 : (61908033679 : ℕ).Prime := by
  refine pock_aux 61908033679 2 36 [(151, 1), (107, 1), (61, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_34 : (6746985142472137 : ℕ).Prime := by
  refine pock_aux 6746985142472137 2 53 [(61908033679, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_33
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_35 : (391244174441674280357 : ℕ).Prime := by
  refine pock_aux 391244174441674280357 2 69 [(6746985142472137, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_34
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_36 : (13468187921 : ℕ).Prime := by
  refine pock_aux 13468187921 2 34 [(58193, 1), (263, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_37 : (1837739119809962086637150154339078793327538933 : ℕ).Prime := by
  refine pock_aux 1837739119809962086637150154339078793327538933 2 151 [(391244174441674280357, 1), (13468187921, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_35
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_36
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_38 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999979529 : ℕ).Prime := by
  refine pock_aux 999999999999999999999999999999999999999999999999999999999999999999999999999999999999979529 2 299 [(1837739119809962086637150154339078793327538933, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_37
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_39 : (298004221211 : ℕ).Prime := by
  refine pock_aux 298004221211 2 39 [(3712523, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_40 : (5960084424221 : ℕ).Prime := by
  refine pock_aux 5960084424221 2 43 [(298004221211, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_39
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_41 : (96051122116051562289412293041047 : ℕ).Prime := by
  refine pock_aux 96051122116051562289412293041047 2 107 [(5960084424221, 1), (6401459, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_40
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_42 : (40379998517 : ℕ).Prime := by
  refine pock_aux 40379998517 2 36 [(6417673, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_43 : (1783235203 : ℕ).Prime := by
  refine pock_aux 1783235203 2 31 [(7309, 1), (157, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_44 : (16780231373911004869565237 : ℕ).Prime := by
  refine pock_aux 16780231373911004869565237 2 84 [(40379998517, 1), (1783235203, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_42
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_43
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_45 : (2416353317843184701217394129 : ℕ).Prime := by
  refine pock_aux 2416353317843184701217394129 2 91 [(16780231373911004869565237, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_44
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_46 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999979943 : ℕ).Prime := by
  refine pock_aux 999999999999999999999999999999999999999999999999999999999999999999999999999999999999979943 2 299 [(96051122116051562289412293041047, 1), (2416353317843184701217394129, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_41
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_45
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_47 : (14402187518775461 : ℕ).Prime := by
  refine pock_aux 14402187518775461 2 54 [(20939, 1), (1021, 1), (659, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_48 : (557262321311455680460234997 : ℕ).Prime := by
  refine pock_aux 557262321311455680460234997 2 89 [(14402187518775461, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_47
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_49 : (856449553799841258494720181816277189 : ℕ).Prime := by
  refine pock_aux 856449553799841258494720181816277189 2 120 [(557262321311455680460234997, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_48
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_50 : (260474283197266118733608000615226112928823155508734633 : ℕ).Prime := by
  refine pock_aux 260474283197266118733608000615226112928823155508734633 2 178 [(856449553799841258494720181816277189, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_49
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_51 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999980191 : ℕ).Prime := by
  refine pock_aux 999999999999999999999999999999999999999999999999999999999999999999999999999999999999980191 2 299 [(260474283197266118733608000615226112928823155508734633, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_50
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_52 : (6891021869 : ℕ).Prime := by
  refine pock_aux 6891021869 2 33 [(3739, 1), (167, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_53 : (2949357359933 : ℕ).Prime := by
  refine pock_aux 2949357359933 2 42 [(6891021869, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_52
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_54 : (2388979461545731 : ℕ).Prime := by
  refine pock_aux 2388979461545731 2 52 [(2949357359933, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_53
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_55 : (64698341777581486943 : ℕ).Prime := by
  refine pock_aux 64698341777581486943 2 66 [(2388979461545731, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_54
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_56 : (11045689098319376939830619 : ℕ).Prime := by
  refine pock_aux 11045689098319376939830619 2 84 [(64698341777581486943, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_55
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_57 : (3510496261263039033777354335055581746252547 : ℕ).Prime := by
  refine pock_aux 3510496261263039033777354335055581746252547 2 142 [(11045689098319376939830619, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_56
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_58 : (1217703981055709668418690102446638181577167733882080874910767946553013167811 : ℕ).Prime := by
  refine pock_aux 1217703981055709668418690102446638181577167733882080874910767946553013167811 2 250 [(3510496261263039033777354335055581746252547, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_57
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_59 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999980293 : ℕ).Prime := by
  refine pock_aux 999999999999999999999999999999999999999999999999999999999999999999999999999999999999980293 2 299 [(1217703981055709668418690102446638181577167733882080874910767946553013167811, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_58
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_60 : (14825663186713 : ℕ).Prime := by
  refine pock_aux 14825663186713 2 44 [(641519, 1), (911, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_61 : (59302652746853 : ℕ).Prime := by
  refine pock_aux 59302652746853 2 46 [(14825663186713, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_60
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_62 : (849368174232076777801 : ℕ).Prime := by
  refine pock_aux 849368174232076777801 2 70 [(59302652746853, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_61
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_63 : (5096209045392460666807 : ℕ).Prime := by
  refine pock_aux 5096209045392460666807 2 73 [(849368174232076777801, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_62
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_64 : (234425616088053190673123 : ℕ).Prime := by
  refine pock_aux 234425616088053190673123 2 78 [(5096209045392460666807, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_63
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_65 : (6120601397927530092211184876350379621 : ℕ).Prime := by
  refine pock_aux 6120601397927530092211184876350379621 2 123 [(234425616088053190673123, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_64
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_66 : (7880834467896997348078131936019614294124672942057 : ℕ).Prime := by
  refine pock_aux 7880834467896997348078131936019614294124672942057 2 163 [(6120601397927530092211184876350379621, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_65
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_67 : (838527452964385765847641738453008513941329382708742172202581567 : ℕ).Prime := by
  refine pock_aux 838527452964385765847641738453008513941329382708742172202581567 2 210 [(7880834467896997348078131936019614294124672942057, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_66
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_68 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999980911 : ℕ).Prime := by
  refine pock_aux 999999999999999999999999999999999999999999999999999999999999999999999999999999999999980911 2 299 [(838527452964385765847641738453008513941329382708742172202581567, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_67
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_69 : (202288903 : ℕ).Prime := by
  refine pock_aux 202288903 2 28 [(265471, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_70 : (19419734689 : ℕ).Prime := by
  refine pock_aux 19419734689 2 35 [(202288903, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_69
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_71 : (184951818490815170387 : ℕ).Prime := by
  refine pock_aux 184951818490815170387 2 68 [(19419734689, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_70
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_72 : (254045985070707012139816818131532881 : ℕ).Prime := by
  refine pock_aux 254045985070707012139816818131532881 2 118 [(184951818490815170387, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_71
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_73 : (19827194462349552447567259136727251708269308417834709 : ℕ).Prime := by
  refine pock_aux 19827194462349552447567259136727251708269308417834709 2 174 [(254045985070707012139816818131532881, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_72
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_74 : (4499613794386287585746112721777949473959361372042039244701239594434966411 : ℕ).Prime := by
  refine pock_aux 4499613794386287585746112721777949473959361372042039244701239594434966411 2 242 [(19827194462349552447567259136727251708269308417834709, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_73
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_75 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999980951 : ℕ).Prime := by
  refine pock_aux 999999999999999999999999999999999999999999999999999999999999999999999999999999999999980951 2 299 [(4499613794386287585746112721777949473959361372042039244701239594434966411, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_74
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_76 : (210369679097 : ℕ).Prime := by
  refine pock_aux 210369679097 2 38 [(1994101, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_77 : (36441311643721242059 : ℕ).Prime := by
  refine pock_aux 36441311643721242059 2 65 [(210369679097, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_76
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_78 : (12932383 : ℕ).Prime := by
  refine pock_aux 12932383 2 24 [(2155397, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_79 : (931131577 : ℕ).Prime := by
  refine pock_aux 931131577 2 30 [(12932383, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_78
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_80 : (416075031765045382585796585433840799003177 : ℕ).Prime := by
  refine pock_aux 416075031765045382585796585433840799003177 2 139 [(36441311643721242059, 1), (931131577, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_77
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_79
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_81 : (56377522662631621253673865021798439631960853712312215504479189940466579891717 : ℕ).Prime := by
  refine pock_aux 56377522662631621253673865021798439631960853712312215504479189940466579891717 2 255 [(416075031765045382585796585433840799003177, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_80
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_82 : (764525993883792048929663608562691131498470948012232415902140672782874617737003058103961 : ℕ).Prime := by
  refine pock_aux 764525993883792048929663608562691131498470948012232415902140672782874617737003058103961 2 289 [(56377522662631621253673865021798439631960853712312215504479189940466579891717, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_81
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_83 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999980989 : ℕ).Prime := by
  refine pock_aux 999999999999999999999999999999999999999999999999999999999999999999999999999999999999980989 2 299 [(764525993883792048929663608562691131498470948012232415902140672782874617737003058103961, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_82
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_84 : (24010582129 : ℕ).Prime := by
  refine pock_aux 24010582129 2 35 [(2263441, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_85 : (6648304422273335733127 : ℕ).Prime := by
  refine pock_aux 6648304422273335733127 2 73 [(24010582129, 1), (292807, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_84
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_86 : (37203911547041586762578693 : ℕ).Prime := by
  refine pock_aux 37203911547041586762578693 2 85 [(6648304422273335733127, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_85
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_87 : (74407823094083173525157387 : ℕ).Prime := by
  refine pock_aux 74407823094083173525157387 2 86 [(37203911547041586762578693, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_86
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_88 : (1566401101698044740980182868264549287681671659983582907944426509039049122509901 : ℕ).Prime := by
  refine pock_aux 1566401101698044740980182868264549287681671659983582907944426509039049122509901 2 260 [(74407823094083173525157387, 1), (254879, 1), (219437, 1), (1373, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_87
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_89 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999981073 : ℕ).Prime := by
  refine pock_aux 999999999999999999999999999999999999999999999999999999999999999999999999999999999999981073 2 299 [(1566401101698044740980182868264549287681671659983582907944426509039049122509901, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_88
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_90 : (3242884597 : ℕ).Prime := by
  refine pock_aux 3242884597 2 32 [(150217, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_91 : (206039572009224719 : ℕ).Prime := by
  refine pock_aux 206039572009224719 2 58 [(3242884597, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_90
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_92 : (36399588067297380986054375692646941 : ℕ).Prime := by
  refine pock_aux 36399588067297380986054375692646941 2 115 [(206039572009224719, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_91
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_93 : (2869233928992783353606722218348587771267 : ℕ).Prime := by
  refine pock_aux 2869233928992783353606722218348587771267 2 132 [(36399588067297380986054375692646941, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_92
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_94 : (7282115711783684151453860990168715763475647 : ℕ).Prime := by
  refine pock_aux 7282115711783684151453860990168715763475647 2 143 [(2869233928992783353606722218348587771267, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_93
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_95 : (2607955895615693888770806674197694690249296613827548004970309 : ℕ).Prime := by
  refine pock_aux 2607955895615693888770806674197694690249296613827548004970309 2 201 [(7282115711783684151453860990168715763475647, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_94
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_96 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999981223 : ℕ).Prime := by
  refine pock_aux 999999999999999999999999999999999999999999999999999999999999999999999999999999999999981223 2 299 [(2607955895615693888770806674197694690249296613827548004970309, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_95
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_97 : (12619222211 : ℕ).Prime := by
  refine pock_aux 12619222211 2 34 [(120103, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_98 : (43612031961217 : ℕ).Prime := by
  refine pock_aux 43612031961217 2 46 [(12619222211, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_97
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_99 : (127748059 : ℕ).Prime := by
  refine pock_aux 127748059 2 27 [(5867, 1), (191, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_100 : (9576505494877 : ℕ).Prime := by
  refine pock_aux 9576505494877 2 44 [(127748059, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_99
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_101 : (47174565282654328629398575086174284051 : ℕ).Prime := by
  refine pock_aux 47174565282654328629398575086174284051 2 126 [(43612031961217, 1), (9576505494877, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_98
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_100
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_102 : (342155899273 : ℕ).Prime := by
  refine pock_aux 342155899273 2 39 [(13399, 1), (491, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_103 : (2157635100815539 : ℕ).Prime := by
  refine pock_aux 2157635100815539 2 51 [(342155899273, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_102
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_104 : (8854934453746972057 : ℕ).Prime := by
  refine pock_aux 8854934453746972057 2 63 [(2157635100815539, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_103
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_105 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999981437 : ℕ).Prime := by
  refine pock_aux 999999999999999999999999999999999999999999999999999999999999999999999999999999999999981437 2 299 [(47174565282654328629398575086174284051, 1), (8854934453746972057, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_101
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_104
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_106 : (173865821919329 : ℕ).Prime := by
  refine pock_aux 173865821919329 2 48 [(16741, 1), (181, 1), (73, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_107 : (7665396356779376953 : ℕ).Prime := by
  refine pock_aux 7665396356779376953 2 63 [(173865821919329, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_106
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_108 : (11874649 : ℕ).Prime := by
  refine pock_aux 11874649 2 24 [(6263, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_109 : (7107456757869055061 : ℕ).Prime := by
  refine pock_aux 7107456757869055061 2 63 [(11874649, 1), (5162501, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_108
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_110 : (161142077904920053109855705391070796401697455189 : ℕ).Prime := by
  refine pock_aux 161142077904920053109855705391070796401697455189 2 157 [(7665396356779376953, 1), (7107456757869055061, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_107
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_109
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_111 : (703462195968214583609906665059200958134089403283565343 : ℕ).Prime := by
  refine pock_aux 703462195968214583609906665059200958134089403283565343 2 179 [(161142077904920053109855705391070796401697455189, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_110
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_112 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999981697 : ℕ).Prime := by
  refine pock_aux 999999999999999999999999999999999999999999999999999999999999999999999999999999999999981697 2 299 [(703462195968214583609906665059200958134089403283565343, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_111
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_113 : (540345529 : ℕ).Prime := by
  refine pock_aux 540345529 2 30 [(7504799, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_114 : (4290297030544507 : ℕ).Prime := by
  refine pock_aux 4290297030544507 2 52 [(540345529, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_113
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_115 : (3310436413 : ℕ).Prime := by
  refine pock_aux 3310436413 2 32 [(419893, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_116 : (153208270277013607625311281700042487 : ℕ).Prime := by
  refine pock_aux 153208270277013607625311281700042487 2 117 [(4290297030544507, 1), (3310436413, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_114
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_115
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_117 : (62211731 : ℕ).Prime := by
  refine pock_aux 62211731 2 26 [(28669, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_118 : (359584678632703241 : ℕ).Prime := by
  refine pock_aux 359584678632703241 2 59 [(62211731, 1), (86579, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_117
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_119 : (273948789138338399554654981 : ℕ).Prime := by
  refine pock_aux 273948789138338399554654981 2 88 [(359584678632703241, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_118
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_120 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999981769 : ℕ).Prime := by
  refine pock_aux 999999999999999999999999999999999999999999999999999999999999999999999999999999999999981769 2 299 [(153208270277013607625311281700042487, 1), (273948789138338399554654981, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_116
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_119
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_121 : (12475182739 : ℕ).Prime := by
  refine pock_aux 12475182739 2 34 [(1223777, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pB (by decide +kernel)
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_122 : (24073475027881326191 : ℕ).Prime := by
  refine pock_aux 24073475027881326191 2 65 [(12475182739, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_121
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_123 : (146174140369295412631753 : ℕ).Prime := by
  refine pock_aux 146174140369295412631753 2 77 [(24073475027881326191, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_122
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_124 : (54940125242243448640447077228216130297 : ℕ).Prime := by
  refine pock_aux 54940125242243448640447077228216130297 2 126 [(146174140369295412631753, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_123
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_125 : (25757728793982656866228694356531246940745960217 : ℕ).Prime := by
  refine pock_aux 25757728793982656866228694356531246940745960217 2 155 [(54940125242243448640447077228216130297, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_124
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

private theorem pch_126 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999981913 : ℕ).Prime := by
  refine pock_aux 999999999999999999999999999999999999999999999999999999999999999999999999999999999999981913 2 299 [(25757728793982656866228694356531246940745960217, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ (by decide +kernel) ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pch_125
    simp at hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide +kernel
    simp at hx

/-- LEAF. First cut of the fourth batch, positions 193 to 196: the four fixed
candidates qs.drop 192 take 4 are prime. This is the four integer tests of the
first cut only, strictly narrower than the whole batch. -/
theorem batch3_prime_part1 : ∀ q ∈ (qs.drop 192).take 4, q.Prime := by
  have hlist : (qs.drop 192).take 4 = [999999999999999999999999999999999999999999999999999999999999999999999999999999999999978683, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999979073, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999979123, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999979159] := by decide +kernel
  intro q hq
  rw [hlist] at hq
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact pch_8
  · exact pch_17
  · exact pch_25
  · exact pch_32

/-- LEAF. Second cut of the fourth batch, positions 197 to 200: the four fixed
candidates (qs.drop 192).drop 4 take 4 are prime. This is the four integer
tests of the second cut only. -/
theorem batch3_prime_part2 : ∀ q ∈ ((qs.drop 192).drop 4).take 4, q.Prime := by
  have hlist : ((qs.drop 192).drop 4).take 4 = [999999999999999999999999999999999999999999999999999999999999999999999999999999999999979529, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999979943, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999980191, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999980293] := by decide +kernel
  intro q hq
  rw [hlist] at hq
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact pch_38
  · exact pch_46
  · exact pch_51
  · exact pch_59

/-- LEAF. Third cut of the fourth batch, positions 201 to 204: the four fixed
candidates (qs.drop 192).drop 8 take 4 are prime. This is the four integer
tests of the third cut only. -/
theorem batch3_prime_part3 : ∀ q ∈ ((qs.drop 192).drop 8).take 4, q.Prime := by
  have hlist : ((qs.drop 192).drop 8).take 4 = [999999999999999999999999999999999999999999999999999999999999999999999999999999999999980911, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999980951, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999980989, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999981073] := by decide +kernel
  intro q hq
  rw [hlist] at hq
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact pch_68
  · exact pch_75
  · exact pch_83
  · exact pch_89

/-- LEAF. Last cut of the fourth batch, positions 205 to 209: the five fixed
candidates (qs.drop 192).drop 12 are prime. This is the five integer tests of
the tail cut only. -/
theorem batch3_prime_part4 : ∀ q ∈ (qs.drop 192).drop 12, q.Prime := by
  have hlist : (qs.drop 192).drop 12 = [999999999999999999999999999999999999999999999999999999999999999999999999999999999999981223, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999981437, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999981697, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999981769, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999981913] := by decide +kernel
  intro q hq
  rw [hlist] at hq
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact pch_96
  · exact pch_105
  · exact pch_112
  · exact pch_120
  · exact pch_126

/-- The fourth fixed candidate batch of row 10^90 consists of primes.
Assembled from the four cut leaves above by re-cutting the list four times;
the proof itself uses no primality beyond the four leaves. -/
theorem batch3_prime_split : ∀ q ∈ qs.drop 192, q.Prime := by
  intro q hq
  have e1 : ((qs.drop 192).drop 4).drop 4 = (qs.drop 192).drop 8 := by
    simp [List.drop_drop]
  have e2 : ((qs.drop 192).drop 8).drop 4 = (qs.drop 192).drop 12 := by
    simp [List.drop_drop]
  rw [← List.take_append_drop 4 (qs.drop 192), List.mem_append] at hq
  rcases hq with hq | hq
  · exact batch3_prime_part1 q hq
  rw [← List.take_append_drop 4 ((qs.drop 192).drop 4), List.mem_append] at hq
  rcases hq with hq | hq
  · exact batch3_prime_part2 q hq
  rw [e1, ← List.take_append_drop 4 ((qs.drop 192).drop 8), List.mem_append] at hq
  rcases hq with hq | hq
  · exact batch3_prime_part3 q hq
  rw [e2] at hq
  exact batch3_prime_part4 q hq

#print axioms batch3_prime_part1
#print axioms batch3_prime_part2
#print axioms batch3_prime_part3
#print axioms batch3_prime_part4
#print axioms batch3_prime_split

end LeanLab.DtRS1998.Decomp395a

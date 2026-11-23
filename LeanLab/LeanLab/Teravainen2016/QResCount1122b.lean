/-
P0076 J. Teravainen, arXiv 1611.08585, Section 5, page 21: the CRT count behind display 5.2
at the modulus q, proving Lemma53Split.leaf_qres_count.
AI wrote the Lean code, Claude, CLOUD burst-20261122 S69. Goldbach is open.
-/
import LeanLab.Teravainen2016.Lemma53Density

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016.QResCount1122b

open LeanLab.Teravainen2016

/-- CRT product count over naturals. -/
theorem card_crt {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (co : a.Coprime b)
    (f g : ℕ → Prop) [DecidablePred f] [DecidablePred g]
    (hf : ∀ x, f x ↔ f (x % a)) (hg : ∀ x, g x ↔ g (x % b)) :
    #((range (a * b)).filter (fun x => f x ∧ g x)) =
      #((range a).filter f) * #((range b).filter g) := by
  rw [← card_product]
  refine card_nbij' (fun x => (x % a, x % b)) (fun u => (Nat.chineseRemainder co u.1 u.2 : ℕ))
    ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_range, Set.mem_setOf_eq, coe_product, Set.mem_prod] at hx ⊢
    refine ⟨⟨Nat.mod_lt _ ha, ?_⟩, ⟨Nat.mod_lt _ hb, ?_⟩⟩
    · rw [hf, Nat.mod_mod]; exact (hf x).mp hx.2.1
    · rw [hg, Nat.mod_mod]; exact (hg x).mp hx.2.2
  · rintro ⟨u, v⟩ huv
    simp only [coe_filter, mem_range, Set.mem_setOf_eq, coe_product, Set.mem_prod] at huv ⊢
    have h1 := (Nat.chineseRemainder co u v).2.1
    have h2 := (Nat.chineseRemainder co u v).2.2
    refine ⟨Nat.chineseRemainder_lt_mul co u v ha.ne' hb.ne', ?_, ?_⟩
    · rw [hf, h1, Nat.mod_eq_of_lt huv.1.1]; exact huv.1.2
    · rw [hg, h2, Nat.mod_eq_of_lt huv.2.1]; exact huv.2.2
  · intro x hx
    simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hx
    have h1 := (Nat.chineseRemainder co (x % a) (x % b)).2.1
    have h2 := (Nat.chineseRemainder co (x % a) (x % b)).2.2
    have hlt := Nat.chineseRemainder_lt_mul co (x % a) (x % b) ha.ne' hb.ne'
    have hm : (Nat.chineseRemainder co (x % a) (x % b) : ℕ) ≡ x [MOD a * b] :=
      (Nat.modEq_and_modEq_iff_modEq_mul co).mp
        ⟨h1.trans (Nat.mod_modEq x a), h2.trans (Nat.mod_modEq x b)⟩
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hx.1] using hm
  · rintro ⟨u, v⟩ huv
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio, coe_filter,
      Set.mem_setOf_eq] at huv
    have h1 := (Nat.chineseRemainder co u v).2.1
    have h2 := (Nat.chineseRemainder co u v).2.2
    simp only [Prod.mk.injEq]
    have e1 : (Nat.chineseRemainder co u v : ℕ) % a = u % a := h1
    have e2 : (Nat.chineseRemainder co u v : ℕ) % b = v % b := h2
    exact ⟨by rw [e1, Nat.mod_eq_of_lt (mem_range.mp huv.1.1)],
      by rw [e2, Nat.mod_eq_of_lt (mem_range.mp huv.2.1)]⟩

/-- Periodic count over naturals. -/
theorem card_periodic {m : ℕ} (hm : 0 < m) (k : ℕ) (f : ℕ → Prop) [DecidablePred f]
    (hf : ∀ x, f x ↔ f (x % m)) :
    #((range (k * m)).filter f) = k * #((range m).filter f) := by
  rw [← card_range k, ← card_product, card_range]
  refine card_nbij' (fun x => (x / m, x % m)) (fun u => u.1 * m + u.2) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_range, Set.mem_setOf_eq, coe_product, coe_range, Set.mem_prod,
      Set.mem_Iio] at hx ⊢
    refine ⟨Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hx.1), Nat.mod_lt _ hm, ?_⟩
    rw [hf, Nat.mod_mod]; exact (hf x).mp hx.2
  · rintro ⟨i, r⟩ h
    simp only [coe_filter, mem_range, Set.mem_setOf_eq, coe_product, coe_range, Set.mem_prod,
      Set.mem_Iio] at h ⊢
    refine ⟨?_, ?_⟩
    · nlinarith
    · rw [hf, Nat.mul_add_mod_of_lt h.2.1]; exact h.2.2
  · intro x _
    exact Nat.div_add_mod' x m
  · rintro ⟨i, r⟩ h
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio, coe_filter,
      Set.mem_setOf_eq] at h
    simp only [Prod.mk.injEq]
    have hr : r < m := mem_range.mp h.2.1
    refine ⟨?_, Nat.mul_add_mod_of_lt hr⟩
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hr, zero_add]

/-- The general sieve count: residues below `q` whose reduction mod every prime `p ∣ q` satisfies
`P p`, times the radical of `q`, equals `q` times the product of the local counts. -/
theorem sieve_count (P : ℕ → ℕ → Prop) [∀ p, DecidablePred (P p)] (q : ℕ) :
    #((range q).filter (fun x => ∀ p ∈ q.primeFactors, P p (x % p))) * ∏ p ∈ q.primeFactors, p =
      q * ∏ p ∈ q.primeFactors, #((range p).filter (P p)) := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    rw [Nat.primeFactors_prime_pow hn.ne' hp]
    simp only [Finset.mem_singleton, forall_eq, prod_singleton]
    have hpos := hp.pos
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ, card_periodic hpos (p ^ k) (fun x => P p (x % p)) (fun x => by rw [Nat.mod_mod]),
      ← pow_succ]
    have : (range p).filter (fun x => P p (x % p)) = (range p).filter (P p) :=
      filter_congr (fun x hx => by rw [Nat.mod_eq_of_lt (mem_range.mp hx)])
    rw [this, pow_succ]; ring
  | zero => simp
  | one => simp
  | coprime a b ha hb co iha ihb =>
    rw [Nat.Coprime.primeFactors_mul co, prod_union (Nat.Coprime.disjoint_primeFactors co),
      prod_union (Nat.Coprime.disjoint_primeFactors co)]
    have hcongr : (range (a * b)).filter (fun x => ∀ p ∈ a.primeFactors ∪ b.primeFactors,
        P p (x % p)) = (range (a * b)).filter (fun x => (∀ p ∈ a.primeFactors, P p (x % p)) ∧
        (∀ p ∈ b.primeFactors, P p (x % p))) :=
      filter_congr (fun x _ => by
        constructor
        · intro h; exact ⟨fun p hp => h p (mem_union_left _ hp), fun p hp => h p (mem_union_right _ hp)⟩
        · rintro ⟨h1, h2⟩ p hp
          rcases mem_union.mp hp with hp | hp
          · exact h1 p hp
          · exact h2 p hp)
    rw [hcongr, card_crt (by omega) (by omega) co]
    · calc _ = (#((range a).filter (fun x => ∀ p ∈ a.primeFactors, P p (x % p))) *
              ∏ p ∈ a.primeFactors, p) *
            (#((range b).filter (fun x => ∀ p ∈ b.primeFactors, P p (x % p))) *
              ∏ p ∈ b.primeFactors, p) := by ring
        _ = _ := by rw [iha, ihb]; ring
    · intro x
      refine forall₂_congr (fun p hp => ?_)
      rw [Nat.mod_mod_of_dvd _ (Nat.dvd_of_mem_primeFactors hp)]
    · intro x
      refine forall₂_congr (fun p hp => ?_)
      rw [Nat.mod_mod_of_dvd _ (Nat.dvd_of_mem_primeFactors hp)]

/-- Shifting a natural number by a multiple of `p` inside `M x + c`. -/
theorem dvd_shift (p x : ℕ) (M c : ℤ) :
    (p : ℤ) ∣ M * x + c ↔ (p : ℤ) ∣ M * ((x % p : ℕ) : ℤ) + c := by
  have h : (x : ℤ) = ((x % p : ℕ) : ℤ) + p * ((x / p : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mod_add_div x p).symm
  have : M * (x : ℤ) + c = (M * ((x % p : ℕ) : ℤ) + c) + p * (M * ((x / p : ℕ) : ℤ)) := by
    rw [h]; ring
  rw [this, dvd_add_left (dvd_mul_right _ _)]

/-- Coprimality to `q` read prime by prime. -/
theorem isCoprime_iff_primeFactors {A : ℤ} {q : ℕ} (hq : q ≠ 0) :
    IsCoprime A (q : ℤ) ↔ ∀ p ∈ q.primeFactors, ¬ (p : ℤ) ∣ A := by
  constructor
  · intro h p hp hpA
    have hu := h.isUnit_of_dvd' hpA (by exact_mod_cast Nat.dvd_of_mem_primeFactors hp)
    rw [Int.isUnit_iff] at hu
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  · intro h
    apply isCoprime_of_primes
    intro p hp hpA hpq
    exact h p (Nat.mem_primeFactors.mpr ⟨hp, by exact_mod_cast hpq, hq⟩) hpA

/-- The local condition of display 5.1 at a prime `p`. -/
def Loc (M b : ℤ) (p r : ℕ) : Prop :=
  ¬ (p : ℤ) ∣ M * r + b ∧ (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ M * r + b - 1)

theorem qres_eq_filter (q : ℕ) (hq : q ≠ 0) (M b : ℤ) :
    QRes q M b = (range q).filter (fun x => ∀ p ∈ q.primeFactors, Loc M b p (x % p)) := by
  unfold QRes
  refine filter_congr (fun x _ => ?_)
  rw [isCoprime_iff_primeFactors hq]
  unfold Loc
  constructor
  · rintro ⟨h1, h2⟩ p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    refine ⟨by rw [← dvd_shift]; exact h1 p hp, fun h4 h3 => ?_⟩
    have := h2 p hpp h4 h3 (Nat.dvd_of_mem_primeFactors hp)
    rwa [sub_eq_add_neg, add_assoc, dvd_shift, ← add_assoc, ← sub_eq_add_neg] at this
  · intro h
    refine ⟨fun p hp => by rw [dvd_shift]; exact (h p hp).1, fun p hpp h4 h3 hpq => ?_⟩
    have hp : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpq, hq⟩
    have := (h p hp).2 h4 h3
    rwa [sub_eq_add_neg, add_assoc, dvd_shift, ← add_assoc, ← sub_eq_add_neg]

/-- Local count at a prime `p` with `M` invertible mod `p`. -/
theorem loc_count (p : ℕ) [hp : Fact p.Prime] (M b : ℤ) (hM : ¬ (p : ℤ) ∣ M) :
    #((range p).filter (Loc M b p)) = p - (if p % 4 = 3 ∧ p ≠ 3 then 2 else 1) := by
  have hc : (M : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have step1 : #((range p).filter (Loc M b p)) =
      #((univ : Finset (ZMod p)).filter (fun y => (M : ZMod p) * y + b ≠ 0 ∧
        (p % 4 = 3 ∧ p ≠ 3 → (M : ZMod p) * y + b ≠ 1))) := by
    refine card_nbij' (fun r => (r : ZMod p)) (fun y => y.val) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_univ, true_and] at hr ⊢
      obtain ⟨_, h1, h2⟩ := hr
      refine ⟨fun h => h1 ?_, fun hc3 h => h2 hc3.1 hc3.2 ?_⟩
      · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact h
      · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h]; ring
    · intro y hy
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_univ, true_and] at hy ⊢
      obtain ⟨h1, h2⟩ := hy
      refine ⟨ZMod.val_lt y, fun h => h1 ?_, fun h4 h3 h => h2 ⟨h4, h3⟩ ?_⟩
      · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h; push_cast at h
        rwa [ZMod.natCast_zmod_val] at h
      · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h; push_cast at h
        rw [ZMod.natCast_zmod_val] at h
        exact sub_eq_zero.mp h
    · intro r hr
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hr
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hr.1]
    · intro y _
      simp only [ZMod.natCast_zmod_val]
  have step2 : #((univ : Finset (ZMod p)).filter (fun y => (M : ZMod p) * y + b ≠ 0 ∧
        (p % 4 = 3 ∧ p ≠ 3 → (M : ZMod p) * y + b ≠ 1))) =
      #((univ : Finset (ZMod p)).filter (fun z => z ≠ 0 ∧ (p % 4 = 3 ∧ p ≠ 3 → z ≠ 1))) := by
    refine card_nbij' (fun y => (M : ZMod p) * y + b) (fun z => (M : ZMod p)⁻¹ * (z - b))
      ?_ ?_ ?_ ?_
    · intro y hy
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hy ⊢
      exact hy
    · intro z hz
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hz ⊢
      rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul, sub_add_cancel]
      exact hz
    · intro y _
      simp only
      rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    · intro z _
      simp only
      rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul, sub_add_cancel]
  rw [step1, step2]
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
  split_ifs with hC
  · have : (univ : Finset (ZMod p)).filter (fun z => z ≠ 0 ∧ (p % 4 = 3 ∧ p ≠ 3 → z ≠ 1)) =
        univ \ {0, 1} := by
      ext z; simp [hC]
    rw [this, card_univ_sdiff, ZMod.card, card_pair h01]
  · have : (univ : Finset (ZMod p)).filter (fun z => z ≠ 0 ∧ (p % 4 = 3 ∧ p ≠ 3 → z ≠ 1)) =
        univ \ {0} := by
      ext z; simp [hC]
    rw [this, card_univ_sdiff, ZMod.card, card_singleton]

/-- Lemma53Split.leaf_qres_count, proved: the CRT count behind display 5.2, page 21. -/
theorem leaf_qres_count_proved (J w : ℕ) (hJ : 5 ≤ J) (hw : wBig ≤ w) (b : ℤ)
    (hb : Amenable (WW J w) b) (q Q' : ℕ) (hq : 1 ≤ q) (hQ' : Q'.Coprime q)
    (hqW : IsCoprime (q : ℤ) (WW J w)) :
    (#(QRes q (WW J w * Q') b) : ℝ) =
      q * ∏ p ∈ q.primeFactors, (1 - (if p % 4 = 3 then (2 : ℝ) else 1) / p) := by
  have hq0 : q ≠ 0 := by omega
  have hw1024 : 1024 ≤ w := by
    have := Lemma53Split.wBig_ge_1024.trans hw
    exact_mod_cast this
  have hbig : ∀ p ∈ q.primeFactors, 1024 < p := fun p hp =>
    lt_of_le_of_lt hw1024 (prime_factor_gt_w hJ hqW hp)
  have hndvd : ∀ p ∈ q.primeFactors, ¬ (p : ℤ) ∣ WW J w * (Q' : ℤ) := by
    intro p hp h
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpq : p ∣ q := Nat.dvd_of_mem_primeFactors hp
    rcases (Nat.prime_iff_prime_int.mp hpp).dvd_or_dvd h with h | h
    · have hu := hqW.isUnit_of_dvd' (by exact_mod_cast hpq) h
      rw [Int.isUnit_iff] at hu
      have := hpp.two_le
      omega
    · have h' : p ∣ Q' := Int.natCast_dvd_natCast.mp h
      have h1 : p ∣ Nat.gcd Q' q := Nat.dvd_gcd h' hpq
      rw [hQ'.gcd_eq_one] at h1
      exact hpp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hloc : ∀ p ∈ q.primeFactors, #((range p).filter (Loc (WW J w * (Q' : ℤ)) b p)) =
      p - (if p % 4 = 3 then 2 else 1) := by
    intro p hp
    haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    rw [loc_count p _ b (hndvd p hp)]
    have h3 : p ≠ 3 := by have := hbig p hp; omega
    by_cases h : p % 4 = 3 <;> simp [h, h3]
  have key := sieve_count (Loc (WW J w * (Q' : ℤ)) b) q
  rw [← qres_eq_filter q hq0, prod_congr rfl hloc] at key
  have hsub : ∀ p ∈ q.primeFactors, ((p - (if p % 4 = 3 then 2 else 1) : ℕ) : ℝ) =
      (p : ℝ) - (if p % 4 = 3 then (2 : ℝ) else 1) := by
    intro p hp
    have := hbig p hp
    split_ifs
    · rw [Nat.cast_sub (by omega)]; norm_num
    · rw [Nat.cast_sub (by omega)]; norm_num
  have key' := congrArg (Nat.cast : ℕ → ℝ) key
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod, prod_congr rfl hsub] at key'
  have hB : (∏ p ∈ q.primeFactors, (p : ℝ)) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun p hp => by have := hbig p hp; positivity)
  have hprod : ∏ p ∈ q.primeFactors, (1 - (if p % 4 = 3 then (2 : ℝ) else 1) / p) =
      (∏ p ∈ q.primeFactors, ((p : ℝ) - (if p % 4 = 3 then (2 : ℝ) else 1))) /
        ∏ p ∈ q.primeFactors, (p : ℝ) := by
    rw [← prod_div_distrib]
    refine prod_congr rfl (fun p hp => ?_)
    have : (p : ℝ) ≠ 0 := by have := hbig p hp; positivity
    field_simp
  rw [hprod, mul_div_assoc', eq_div_iff hB, key']

/-- Twin check against the LEAF's own statement. -/
theorem leaf_qres_count_twin : type_of% @Lemma53Split.leaf_qres_count :=
  leaf_qres_count_proved

end LeanLab.Teravainen2016.QResCount1122b

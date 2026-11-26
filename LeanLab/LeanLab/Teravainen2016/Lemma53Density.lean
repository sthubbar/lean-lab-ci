/-
P0076, Section 5, page 21, the local density step in the proof of Lemma 5.3.
Split of Lemma53Split.local_density into the exact CRT count of the set of display 5.1 at the
modulus q, a cited LEAF, and the proved bound q times the product of 1 - omega p / p over the
primes of q is at least q^(9/10), since every such prime exceeds w.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.Lemma53Split

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016.Lemma53Split

open LeanLab.Teravainen2016

/-- Divisibility of a linear form by a prime depends only on the argument modulo a multiple
of that prime. -/
private theorem dvd_iff_dvd_mod (K b : ℤ) {d p : ℕ} (hpd : p ∣ d) (c : ℕ) :
    ((p : ℤ) ∣ K * (c : ℤ) + b) ↔ ((p : ℤ) ∣ K * ((c % d : ℕ) : ℤ) + b) := by
  have hsum : ((c % d : ℕ) : ℤ) + ((d * (c / d) : ℕ) : ℤ) = (c : ℤ) := by
    rw [← Nat.cast_add, Nat.mod_add_div]
  have hdec : (c : ℤ) = ((c % d : ℕ) : ℤ) + (d : ℤ) * ((c / d : ℕ) : ℤ) := by
    rw [← hsum, Nat.cast_mul]
  have hpd' : (p : ℤ) ∣ (d : ℤ) := by exact_mod_cast hpd
  have hK : (p : ℤ) ∣ K * ((d : ℤ) * ((c / d : ℕ) : ℤ)) :=
    (hpd'.mul_right ((c / d : ℕ) : ℤ)).mul_left K
  have hsplit : K * (c : ℤ) + b
      = (K * ((c % d : ℕ) : ℤ) + b) + K * ((d : ℤ) * ((c / d : ℕ) : ℤ)) := by
    rw [hdec]; ring
  constructor
  · intro h
    have h2 := dvd_sub h hK
    rwa [hsplit, add_sub_cancel_right] at h2
  · intro h
    rw [hsplit]
    exact dvd_add h hK

/-- The local condition of display (5.1) at a prime `p` depends only on the argument modulo
any multiple of `p`. -/
private theorem cond_iff_cond_mod (K b : ℤ) {d p c : ℕ} (hpd : p ∣ d) :
    ((¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
        (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1)) ↔
      (¬ (p : ℤ) ∣ K * ((c % d : ℕ) : ℤ) + b ∧
        (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * ((c % d : ℕ) : ℤ) + b - 1))) := by
  have h1 : ((p : ℤ) ∣ K * (c : ℤ) + b) ↔ ((p : ℤ) ∣ K * ((c % d : ℕ) : ℤ) + b) :=
    dvd_iff_dvd_mod K b hpd c
  have h2 : ((p : ℤ) ∣ K * (c : ℤ) + b - 1) ↔
      ((p : ℤ) ∣ K * ((c % d : ℕ) : ℤ) + b - 1) := by
    have h := dvd_iff_dvd_mod K (b - 1) hpd c
    have e1 : K * (c : ℤ) + b - 1 = K * (c : ℤ) + (b - 1) := by ring
    have e2 : K * ((c % d : ℕ) : ℤ) + b - 1 = K * ((c % d : ℕ) : ℤ) + (b - 1) := by ring
    rw [e1, e2]
    exact h
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨fun h => ha (h1.mpr h), fun h4 h43 h => hb h4 h43 (h2.mpr h)⟩
  · rintro ⟨ha, hb⟩
    exact ⟨fun h => ha (h1.mp h), fun h4 h43 h => hb h4 h43 (h2.mp h)⟩

/-- Counting over a product of coprime moduli: the CRT splits the filter over `insert p S'`
into a product of the filtered ranges. -/
private theorem card_insert_mul_concrete (K b : ℤ) {p : ℕ} {S' : Finset ℕ}
    (hpS' : p ∉ S') {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : x.Coprime y)
    (hpx : p ∣ x) (hyS : ∀ q ∈ S', q ∣ y) :
    #((Finset.range (x * y)).filter (fun c : ℕ => ∀ p₀ ∈ insert p S',
        (¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b ∧
          (p₀ % 4 = 3 → p₀ ≠ 3 → ¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b - 1))))
      = #((Finset.range x).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
          (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1)))
        * #((Finset.range y).filter (fun c : ℕ => ∀ p₀ ∈ S',
        (¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b ∧
          (p₀ % 4 = 3 → p₀ ≠ 3 → ¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b - 1)))) := by
  classical
  have hx0 : x ≠ 0 := by omega
  have hy0 : y ≠ 0 := by omega
  have hmain : #((Finset.range (x * y)).filter (fun c : ℕ => ∀ p₀ ∈ insert p S',
        (¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b ∧
          (p₀ % 4 = 3 → p₀ ≠ 3 → ¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b - 1))))
      = #(((Finset.range x).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
            (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1))) ×ˢ
          ((Finset.range y).filter (fun c : ℕ => ∀ p₀ ∈ S',
            (¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b ∧
              (p₀ % 4 = 3 → p₀ ≠ 3 → ¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b - 1))))) := by
    apply Finset.card_bij (fun c _ => (c % x, c % y))
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_range] at hc
      obtain ⟨hclt, hcond⟩ := hc
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨Nat.mod_lt c (by omega), ?_⟩, Nat.mod_lt c (by omega), fun q hq => ?_⟩
      · exact (cond_iff_cond_mod K b hpx).mp
          (hcond p (Finset.mem_insert_self p S'))
      · exact (cond_iff_cond_mod K b (hyS q hq)).mp
          (hcond q (Finset.mem_insert_of_mem hq))
    · intro c1 hc1 c2 hc2 heq
      simp only [Finset.mem_filter, Finset.mem_range] at hc1 hc2
      have e1 : c1 % x = c2 % x := congrArg Prod.fst heq
      have e2 : c1 % y = c2 % y := congrArg Prod.snd heq
      have hm : c1 ≡ c2 [MOD x * y] :=
        (Nat.modEq_and_modEq_iff_modEq_mul hxy).mp ⟨e1, e2⟩
      exact hm.eq_of_lt_of_lt hc1.1 hc2.1
    · intro v hv
      obtain ⟨u, v'⟩ := v
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hv
      obtain ⟨⟨hu, hcu⟩, hv', hcv⟩ := hv
      set a : ℕ := (Nat.chineseRemainder hxy u v').val with ha
      have ham : a % x = u := by
        have h2 : a % x = u % x := (Nat.chineseRemainder hxy u v').prop.1
        rw [Nat.mod_eq_of_lt hu] at h2
        exact h2
      have han : a % y = v' := by
        have h2 : a % y = v' % y := (Nat.chineseRemainder hxy u v').prop.2
        rw [Nat.mod_eq_of_lt hv'] at h2
        exact h2
      have halt : a < x * y := Nat.chineseRemainder_lt_mul hxy u v' hx0 hy0
      refine ⟨a, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨halt, fun q hq => ?_⟩
        rcases Finset.mem_insert.mp hq with hq' | hq'
        · subst hq'
          exact (cond_iff_cond_mod K b hpx).mpr
            (by rw [ham]; exact hcu)
        · exact (cond_iff_cond_mod K b (hyS q hq')).mpr
            (by rw [han]; exact hcv q hq')
      · show (a % x, a % y) = (u, v')
        rw [ham, han]
  rw [hmain, Finset.card_product]

/-- Counting modulo a prime power: the condition depends only on the residue modulo `p`, and
each residue modulo `p` occurs `p^(k-1)` times below `p^k`. -/
private theorem card_pow_concrete (K b : ℤ) {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    #((Finset.range (p ^ k)).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
        (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1)))
      = #((Finset.range p).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
          (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1))) * p ^ (k - 1) := by
  classical
  have hp0 : 0 < p := hp.pos
  have hpk : p ^ k = p * p ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [Nat.pow_succ']
  have hmain : #((Finset.range (p ^ k)).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
        (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1)))
      = #(((Finset.range p).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
          (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1))) ×ˢ
          (Finset.range (p ^ (k - 1)))) := by
    apply Finset.card_bij (fun c _ => (c % p, c / p))
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_range] at hc
      obtain ⟨hclt, hcP⟩ := hc
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨Nat.mod_lt c hp0, (cond_iff_cond_mod K b (dvd_refl p)).mp hcP⟩, ?_⟩
      rw [Nat.div_lt_iff_lt_mul hp0, Nat.mul_comm (p ^ (k - 1)) p, ← hpk]
      exact hclt
    · intro c1 hc1 c2 hc2 heq
      have e1 : c1 % p = c2 % p := congrArg Prod.fst heq
      have e2 : c1 / p = c2 / p := congrArg Prod.snd heq
      calc c1 = p * (c1 / p) + c1 % p := (Nat.div_add_mod c1 p).symm
        _ = p * (c2 / p) + c2 % p := by rw [e2, e1]
        _ = c2 := Nat.div_add_mod c2 p
    · intro v hv
      obtain ⟨a, j⟩ := v
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hv
      obtain ⟨⟨ha1, haP⟩, hj1⟩ := hv
      refine ⟨a + p * j, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, ?_⟩
        · rw [hpk]
          calc a + p * j < p * (1 + j) := by
                have h1 : a + p * j < p + p * j := by omega
                have h2 : p + p * j = p * (1 + j) := by ring
                rwa [h2] at h1
            _ ≤ p * p ^ (k - 1) := Nat.mul_le_mul_left p (by omega)
        · exact (cond_iff_cond_mod K b (dvd_refl p)).mpr
            (by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha1]; exact haP)
      · show ((a + p * j) % p, (a + p * j) / p) = (a, j)
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha1]
        rw [Nat.add_mul_div_left a j hp0, Nat.div_eq_of_lt ha1, Nat.zero_add]
  rw [hmain, Finset.card_product, Finset.card_range]

/-- Exactly one residue modulo the prime `p` solves `K c + b = 0`, when `p` does not divide
`K`. -/
private theorem card_linear_dvd_eq_one (K : ℤ) {p : ℕ} (hp : p.Prime)
    (hK : ¬ (p : ℤ) ∣ K) (b : ℤ) :
    #((Finset.range p).filter (fun c : ℕ => (p : ℤ) ∣ K * (c : ℤ) + b)) = 1 := by
  classical
  set A : Finset ℕ := (Finset.range p).filter (fun c : ℕ => (p : ℤ) ∣ K * (c : ℤ) + b) with hA
  have huniq : ∀ a ∈ A, ∀ a' ∈ A, a = a' := by
    intro a ha a' ha'
    rw [hA, Finset.mem_filter, Finset.mem_range] at ha ha'
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨ha1', ha2'⟩ := ha'
    have hd : (p : ℤ) ∣ K * ((a : ℤ) - (a' : ℤ)) := by
      have h := dvd_sub ha2 ha2'
      have e : K * (a : ℤ) + b - (K * (a' : ℤ) + b) = K * ((a : ℤ) - (a' : ℤ)) := by ring
      rwa [e] at h
    have hpint : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpint.dvd_mul.mp hd with h | h
    · exact absurd h hK
    · have hmod : a ≡ a' [MOD p] := by
        rw [Nat.modEq_iff_dvd]
        simpa using dvd_neg.mpr h
      exact hmod.eq_of_lt_of_lt ha1 ha1'
  have hne : A.Nonempty := by
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero p := ⟨hp.pos.ne'⟩
    have hK0 : ((K : ℤ) : ZMod p) ≠ 0 := by
      intro h
      exact hK ((ZMod.intCast_zmod_eq_zero_iff_dvd K p).mp h)
    set x : ZMod p := (-((b : ℤ) : ZMod p)) * ((K : ℤ) : ZMod p)⁻¹ with hx
    have hzero : ((K : ℤ) : ZMod p) * x = -((b : ℤ) : ZMod p) := by
      rw [hx]
      have hring : ((K : ℤ) : ZMod p) * (-((b : ℤ) : ZMod p) * ((K : ℤ) : ZMod p)⁻¹)
          = -((b : ℤ) : ZMod p) * (((K : ℤ) : ZMod p) * ((K : ℤ) : ZMod p)⁻¹) := by ring
      rw [hring, mul_inv_cancel₀ hK0, mul_one]
    have hxval : (((x.val : ℕ)) : ZMod p) = x := ZMod.natCast_zmod_val x
    refine ⟨x.val, ?_⟩
    rw [hA, Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt x, ?_⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hcast : (((K * ((x.val : ℕ) : ℤ) + b : ℤ)) : ZMod p)
        = ((K : ℤ) : ZMod p) * x + ((b : ℤ) : ZMod p) := by
      push_cast
      rw [hxval]
    rw [hcast, hzero]
    ring
  exact Nat.le_antisymm (Finset.card_le_one.mpr huniq)
    (Nat.succ_le_of_lt (Finset.card_pos.mpr hne))

/-- The number of residues modulo the prime `p ≠ 3` satisfying the two local conditions of
display (5.1) is `p - omega p` with `omega p = 2` for `p = 3 mod 4` and `1` otherwise. -/
private theorem card_residues_prime (K b : ℤ) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hK : ¬ (p : ℤ) ∣ K) :
    #((Finset.range p).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
        (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1)))
      = p - (if p % 4 = 3 then 2 else 1) := by
  classical
  set A0 : Finset ℕ := (Finset.range p).filter (fun c : ℕ => (p : ℤ) ∣ K * (c : ℤ) + b) with hA0
  set A1 : Finset ℕ :=
    (Finset.range p).filter (fun c : ℕ => (p : ℤ) ∣ K * (c : ℤ) + b - 1) with hA1
  have h0 : #A0 = 1 := card_linear_dvd_eq_one K hp hK b
  have h1 : #A1 = 1 := by
    rw [hA1]
    have hfil : (Finset.range p).filter (fun c : ℕ => (p : ℤ) ∣ K * (c : ℤ) + b - 1)
        = (Finset.range p).filter (fun c : ℕ => (p : ℤ) ∣ K * (c : ℤ) + (b - 1)) :=
      Finset.filter_congr (fun c _ => by
        have e : K * (c : ℤ) + b - 1 = K * (c : ℤ) + (b - 1) := by ring
        rw [e])
    rw [hfil]
    exact card_linear_dvd_eq_one K hp hK (b - 1)
  have hdisj : Disjoint A0 A1 := by
    rw [Finset.disjoint_left]
    intro c hc0 hc1
    rw [hA0, Finset.mem_filter] at hc0
    rw [hA1, Finset.mem_filter] at hc1
    have hd : (p : ℤ) ∣ 1 := by
      have h := dvd_sub hc0.2 hc1.2
      have e' : K * (c : ℤ) + b - (K * (c : ℤ) + b - 1) = 1 := by ring
      rwa [e'] at h
    have : p ∣ 1 := by exact_mod_cast hd
    exact hp.not_dvd_one this
  have hsubU : A0 ∪ A1 ⊆ Finset.range p := by
    intro c hc
    rcases Finset.mem_union.mp hc with h | h
    · rw [hA0, Finset.mem_filter] at h; exact h.1
    · rw [hA1, Finset.mem_filter] at h; exact h.1
  have hsub0 : A0 ⊆ Finset.range p := by
    intro c hc
    rw [hA0, Finset.mem_filter] at hc; exact hc.1
  by_cases h43 : p % 4 = 3
  · have hguard : ∀ c : ℕ, (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1)
        ↔ ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1 := by
      intro c
      exact ⟨fun h => h h43 hp3, fun h _ _ => h⟩
    have hT1 : (Finset.range p).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
        (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1))
        = (Finset.range p).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
          ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1) :=
      Finset.filter_congr (fun c _ => by rw [hguard c])
    have hT2 : (Finset.range p).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
        ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1) = Finset.range p \ (A0 ∪ A1) := by
      ext c
      rw [Finset.mem_filter, Finset.mem_sdiff, hA0, hA1, Finset.mem_union,
        Finset.mem_filter, Finset.mem_filter, not_or, not_and, not_and]
      constructor
      · rintro ⟨hlt, hP0, hP1⟩
        exact ⟨hlt, fun _ => hP0, fun _ => hP1⟩
      · rintro ⟨hlt, hQ0, hQ1⟩
        exact ⟨hlt, hQ0 hlt, hQ1 hlt⟩
    rw [hT1, hT2, if_pos h43, Finset.card_sdiff_of_subset hsubU,
      Finset.card_union_of_disjoint hdisj, h0, h1, Finset.card_range]
  · have hguard : ∀ c : ℕ, (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1) :=
      fun c h => absurd h h43
    have hT1 : (Finset.range p).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b ∧
        (p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ K * (c : ℤ) + b - 1))
        = (Finset.range p).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b) :=
      Finset.filter_congr (fun c _ => by
        constructor
        · rintro ⟨h, _⟩; exact h
        · intro h; exact ⟨h, hguard c⟩)
    have hT2 : (Finset.range p).filter (fun c : ℕ => ¬ (p : ℤ) ∣ K * (c : ℤ) + b)
        = Finset.range p \ A0 := by
      ext c
      rw [Finset.mem_filter, Finset.mem_sdiff, hA0, Finset.mem_filter, not_and]
      constructor
      · rintro ⟨hlt, hP0⟩
        exact ⟨hlt, fun _ => hP0⟩
      · rintro ⟨hlt, hQ0⟩
        exact ⟨hlt, hQ0 hlt⟩
    rw [hT1, hT2, if_neg h43, Finset.card_sdiff_of_subset hsub0, h0, Finset.card_range]

/-- The count of residues modulo `∏ x ∈ S, x^(e x)` satisfying the conditions of display (5.1)
at every prime of `S` is the product of the local counts. -/
private theorem card_prod_pow (K b : ℤ) (e : ℕ → ℕ) (S : Finset ℕ)
    (hSp : ∀ p ∈ S, p.Prime) (hS3 : ∀ p ∈ S, p ≠ 3)
    (hSe : ∀ p ∈ S, 1 ≤ e p) (hKS : ∀ p ∈ S, ¬ (p : ℤ) ∣ K) :
    #((Finset.range (∏ x ∈ S, x ^ e x)).filter (fun c : ℕ => ∀ p₀ ∈ S,
        (¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b ∧
          (p₀ % 4 = 3 → p₀ ≠ 3 → ¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b - 1))))
      = ∏ x ∈ S, (x ^ e x - (if x % 4 = 3 then 2 else 1) * x ^ (e x - 1)) := by
  classical
  revert hSp hS3 hSe hKS
  induction S using Finset.induction with
  | empty =>
      intro hSp hS3 hSe hKS
      rw [Finset.prod_empty]
      rw [show (Finset.range 1).filter (fun c : ℕ => ∀ p₀ ∈ (∅ : Finset ℕ),
          (¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b ∧
            (p₀ % 4 = 3 → p₀ ≠ 3 → ¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b - 1))) = Finset.range 1 from
        Finset.filter_true_of_mem (fun c _ => by simp)]
      rw [Finset.card_range, Finset.prod_empty]
  | insert p S' hpS' ih =>
      intro hSp hS3 hSe hKS
      have hpp : p.Prime := hSp p (Finset.mem_insert_self p S')
      have hSp' : ∀ q ∈ S', q.Prime := fun q hq => hSp q (Finset.mem_insert_of_mem hq)
      have hS3p : p ≠ 3 := hS3 p (Finset.mem_insert_self p S')
      have hS3' : ∀ q ∈ S', q ≠ 3 := fun q hq => hS3 q (Finset.mem_insert_of_mem hq)
      have hSep : 1 ≤ e p := hSe p (Finset.mem_insert_self p S')
      have hSep0 : e p ≠ 0 := by omega
      have hSe' : ∀ q ∈ S', 1 ≤ e q := fun q hq => hSe q (Finset.mem_insert_of_mem hq)
      have hKp : ¬ (p : ℤ) ∣ K := hKS p (Finset.mem_insert_self p S')
      have hK' : ∀ q ∈ S', ¬ (q : ℤ) ∣ K := fun q hq => hKS q (Finset.mem_insert_of_mem hq)
      have hcop : (p ^ e p).Coprime (∏ x ∈ S', x ^ e x) := by
        rw [Nat.coprime_prod_right_iff]
        intro q hq
        have hpq : p ≠ q := fun h => hpS' (h ▸ hq)
        exact (((Nat.coprime_primes hpp (hSp' q hq)).mpr hpq).pow_left (e p)).pow_right (e q)
      have hx1 : 1 ≤ p ^ e p := Nat.succ_le_of_lt (pow_pos hpp.pos _)
      have hy1 : 1 ≤ ∏ x ∈ S', x ^ e x :=
        Nat.succ_le_of_lt (Finset.prod_pos (fun q hq => pow_pos (hSp' q hq).pos _))
      have hpx : p ∣ p ^ e p := dvd_pow_self p hSep0
      have hyS : ∀ q ∈ S', q ∣ ∏ x ∈ S', x ^ e x := by
        intro q hq
        have hq0 : e q ≠ 0 := by have := hSe' q hq; omega
        exact (dvd_pow_self q hq0).trans (Finset.dvd_prod_of_mem (fun x => x ^ e x) hq)
      rw [Finset.prod_insert hpS', Finset.prod_insert hpS']
      refine (card_insert_mul_concrete K b hpS' hx1 hy1 hcop hpx hyS).trans ?_
      rw [card_pow_concrete K b hpp hSep, card_residues_prime K b hpp hS3p hKp]
      have hS'val : #((Finset.range (∏ x ∈ S', x ^ e x)).filter (fun c : ℕ => ∀ p₀ ∈ S',
          (¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b ∧
            (p₀ % 4 = 3 → p₀ ≠ 3 → ¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b - 1))))
          = ∏ x ∈ S', (x ^ e x - (if x % 4 = 3 then 2 else 1) * x ^ (e x - 1)) :=
        ih hSp' hS3' hSe' hK'
      rw [hS'val]
      have harith : p ^ e p - (if p % 4 = 3 then 2 else 1) * p ^ (e p - 1)
          = (p - (if p % 4 = 3 then 2 else 1)) * p ^ (e p - 1) := by
        have hpk : p ^ e p = p * p ^ (e p - 1) := by
          conv_lhs => rw [show e p = (e p - 1) + 1 by omega]
          rw [Nat.pow_succ']
        rw [hpk, Nat.sub_mul]
      rw [harith]

/-- The same count for a modulus given as the product, needed to read off the count at `q`. -/
private theorem card_count_of_eq_prod (K b : ℤ) (N : ℕ) (S : Finset ℕ) (e : ℕ → ℕ)
    (hN : N = ∏ x ∈ S, x ^ e x) (hSp : ∀ p ∈ S, p.Prime) (hS3 : ∀ p ∈ S, p ≠ 3)
    (hSe : ∀ p ∈ S, 1 ≤ e p) (hKS : ∀ p ∈ S, ¬ (p : ℤ) ∣ K) :
    #((Finset.range N).filter (fun c : ℕ => ∀ p₀ ∈ S,
        (¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b ∧
          (p₀ % 4 = 3 → p₀ ≠ 3 → ¬ (p₀ : ℤ) ∣ K * (c : ℤ) + b - 1))))
      = ∏ x ∈ S, (x ^ e x - (if x % 4 = 3 then 2 else 1) * x ^ (e x - 1)) := by
  subst hN
  exact card_prod_pow K b e S hSp hS3 hSe hKS

theorem leaf_qres_count (J w : ℕ) (hJ : 5 ≤ J) (hw : wBig ≤ w) (b : ℤ)
    (hb : Amenable (WW J w) b) (q Q' : ℕ) (hq : 1 ≤ q) (hQ' : Q'.Coprime q)
    (hqW : IsCoprime (q : ℤ) (WW J w)) :
    (#(QRes q (WW J w * Q') b) : ℝ) =
      q * ∏ p ∈ q.primeFactors, (1 - (if p % 4 = 3 then (2 : ℝ) else 1) / p) := by
  classical
  have hq0 : q ≠ 0 := by omega
  have h3W : (3 : ℤ) ∣ WW J w := by
    show (3 : ℤ) ∣ Wmod J (Sw w)
    exact (by norm_num : (3 : ℤ) ∣ 27).trans (dvd27_Wmod J (Sw w))
  have hne3 : ∀ p ∈ q.primeFactors, p ≠ 3 := by
    intro p hp hp3
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpq : (p : ℤ) ∣ (q : ℤ) := by exact_mod_cast Nat.dvd_of_mem_primeFactors hp
    have hpW : (p : ℤ) ∣ WW J w := by rw [hp3]; exact h3W
    have hg : (p : ℤ) ∣ ((Int.gcd (q : ℤ) (WW J w) : ℕ) : ℤ) := by
      exact_mod_cast Int.dvd_gcd hpq hpW
    rw [Int.isCoprime_iff_gcd_eq_one.mp hqW] at hg
    have h1 : (p : ℤ) ∣ (1 : ℤ) := by simpa using hg
    exact hpp.not_dvd_one (by exact_mod_cast h1)
  have hfac1 : ∀ p ∈ q.primeFactors, 1 ≤ q.factorization p := by
    intro p hp
    exact Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hq0
      (Nat.dvd_of_mem_primeFactors hp)
  have hKW : ∀ p ∈ q.primeFactors, ¬ (p : ℤ) ∣ WW J w * (Q' : ℤ) := by
    intro p hp hdvd
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpq : (p : ℤ) ∣ (q : ℤ) := by exact_mod_cast Nat.dvd_of_mem_primeFactors hp
    rcases (Nat.prime_iff_prime_int.mp hpp).dvd_mul.mp hdvd with h | h
    · have hg : (p : ℤ) ∣ ((Int.gcd (q : ℤ) (WW J w) : ℕ) : ℤ) := by
        exact_mod_cast Int.dvd_gcd hpq h
      rw [Int.isCoprime_iff_gcd_eq_one.mp hqW] at hg
      have h1 : (p : ℤ) ∣ (1 : ℤ) := by simpa using hg
      exact hpp.not_dvd_one (by exact_mod_cast h1)
    · have hpq' : p ∣ Q' := by exact_mod_cast h
      have h1 : p ∣ Nat.gcd Q' q := Nat.dvd_gcd hpq' (Nat.dvd_of_mem_primeFactors hp)
      rw [hQ'] at h1
      exact hpp.not_dvd_one h1
  have hN : q = ∏ p ∈ q.primeFactors, p ^ q.factorization p :=
    Nat.prod_primeFactors_pow_factorization hq0
  have hcount := card_count_of_eq_prod (WW J w * (Q' : ℤ)) b q q.primeFactors
    (fun p => q.factorization p) hN (fun p hp => Nat.prime_of_mem_primeFactors hp) hne3 hfac1 hKW
  have hcop_iff : ∀ c : ℕ, (IsCoprime (WW J w * (Q' : ℤ) * (c : ℤ) + b) (q : ℤ) ↔
      ∀ p ∈ q.primeFactors, ¬ (p : ℤ) ∣ WW J w * (Q' : ℤ) * (c : ℤ) + b) := by
    intro c
    constructor
    · intro hc p hp hdvd
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpq : (p : ℤ) ∣ (q : ℤ) := by exact_mod_cast Nat.dvd_of_mem_primeFactors hp
      have hg : (p : ℤ) ∣
          ((Int.gcd (WW J w * (Q' : ℤ) * (c : ℤ) + b) (q : ℤ) : ℕ) : ℤ) := by
        exact_mod_cast Int.dvd_gcd hdvd hpq
      rw [Int.isCoprime_iff_gcd_eq_one.mp hc] at hg
      have h1 : (p : ℤ) ∣ (1 : ℤ) := by simpa using hg
      exact hpp.not_dvd_one (by exact_mod_cast h1)
    · intro h
      rw [Int.isCoprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd hne
      have h2 := Int.dvd_gcd_iff.mp hpd
      have hmem : p ∈ q.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpp, by exact_mod_cast h2.2, hq0⟩
      exact h p hmem h2.1
  have hQRes : QRes q (WW J w * (Q' : ℤ)) b = (Finset.range q).filter (fun c : ℕ =>
      ∀ p₀ ∈ q.primeFactors,
        (¬ (p₀ : ℤ) ∣ WW J w * (Q' : ℤ) * (c : ℤ) + b ∧
          (p₀ % 4 = 3 → p₀ ≠ 3 → ¬ (p₀ : ℤ) ∣ WW J w * (Q' : ℤ) * (c : ℤ) + b - 1))) := by
    ext c
    simp only [QRes, mem_filter, mem_range]
    constructor
    · rintro ⟨hlt, hcop, hcond⟩
      refine ⟨hlt, fun p hp => ⟨(hcop_iff c).mp hcop p hp, ?_⟩⟩
      intro h4 h43 hdvd
      exact hcond p (Nat.prime_of_mem_primeFactors hp) h4 h43
        (Nat.dvd_of_mem_primeFactors hp) hdvd
    · rintro ⟨hlt, hcond⟩
      refine ⟨hlt, (hcop_iff c).mpr (fun p hp => (hcond p hp).1), ?_⟩
      intro p hpp h4 h43 hpq hdvd
      exact (hcond p (Nat.mem_primeFactors.mpr ⟨hpp, hpq, hq0⟩)).2 h4 h43 hdvd
  have hfac : ∀ x ∈ q.primeFactors,
      ((x ^ q.factorization x - (if x % 4 = 3 then 2 else 1) * x ^ (q.factorization x - 1) :
          ℕ) : ℝ)
        = ((x : ℝ) ^ q.factorization x) *
            (1 - (if x % 4 = 3 then (2 : ℝ) else 1) / (x : ℝ)) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hk1 : 1 ≤ q.factorization p := hfac1 p hp
    set c : ℕ := if p % 4 = 3 then 2 else 1 with hc
    have hcle : c * p ^ (q.factorization p - 1) ≤ p ^ q.factorization p := by
      have hpk : p ^ q.factorization p = p * p ^ (q.factorization p - 1) := by
        conv_lhs => rw [show q.factorization p = (q.factorization p - 1) + 1 by omega]
        rw [Nat.pow_succ']
      rw [hpk]
      have hc2 : c ≤ 2 := by
        rw [hc]; split_ifs <;> norm_num
      calc c * p ^ (q.factorization p - 1) ≤ 2 * p ^ (q.factorization p - 1) :=
            Nat.mul_le_mul_right _ hc2
        _ ≤ p * p ^ (q.factorization p - 1) := Nat.mul_le_mul_right _ hpp.two_le
    rw [Nat.cast_sub hcle, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
    have hccast : ((c : ℕ) : ℝ) = (if p % 4 = 3 then (2 : ℝ) else 1) := by
      rw [hc]; split_ifs <;> norm_num
    rw [hccast]
    have hp0 : (p : ℝ) ≠ 0 := by
      have hpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
      linarith
    have hpk : (p : ℝ) ^ q.factorization p
        = (p : ℝ) * (p : ℝ) ^ (q.factorization p - 1) := by
      conv_lhs => rw [show q.factorization p = (q.factorization p - 1) + 1 by omega]
      rw [pow_succ']
    have hWp : ((p : ℝ) * (p : ℝ) ^ (q.factorization p - 1)) *
        ((if p % 4 = 3 then (2 : ℝ) else 1) / (p : ℝ))
        = (if p % 4 = 3 then (2 : ℝ) else 1) * (p : ℝ) ^ (q.factorization p - 1) := by
      rw [mul_div_assoc']
      have hr : ((p : ℝ) * (p : ℝ) ^ (q.factorization p - 1)) *
          (if p % 4 = 3 then (2 : ℝ) else 1)
          = (p : ℝ) * ((if p % 4 = 3 then (2 : ℝ) else 1) *
              (p : ℝ) ^ (q.factorization p - 1)) := by ring
      rw [hr]
      exact mul_div_cancel_left₀ _ hp0
    rw [hpk, mul_sub, mul_one, hWp]
  have hcard : #(QRes q (WW J w * (Q' : ℤ)) b)
      = ∏ x ∈ q.primeFactors,
          (x ^ q.factorization x - (if x % 4 = 3 then 2 else 1) * x ^ (q.factorization x - 1)) := by
    rw [hQRes]
    exact hcount
  rw [hcard, Nat.cast_prod]
  trans ∏ x ∈ q.primeFactors,
      (((x : ℝ) ^ q.factorization x) * (1 - (if x % 4 = 3 then (2 : ℝ) else 1) / (x : ℝ)))
  · exact Finset.prod_congr rfl (fun p hp => hfac p hp)
  · rw [Finset.prod_mul_distrib]
    have hcast : ((∏ x ∈ q.primeFactors, x ^ q.factorization x : ℕ) : ℝ)
        = ∏ x ∈ q.primeFactors, ((x : ℝ) ^ q.factorization x) := by
      rw [Nat.cast_prod]
      simp
    have hqprod : (∏ x ∈ q.primeFactors, ((x : ℝ) ^ q.factorization x)) = (q : ℝ) := by
      rw [← hcast]
      exact congrArg (fun n : ℕ => (n : ℝ)) hN.symm
    rw [hqprod]

/-- wBig is at least 1024. -/
theorem wBig_ge_1024 : (1024 : ℝ) ≤ wBig := by
  unfold wBig
  have h : (10 : ℝ) ^ ((4 : ℝ)) ≤ (10 : ℝ) ^ ((10 : ℝ) ^ (10 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (10 : ℝ) ^ (1 : ℝ) ≤ (10 : ℝ) ^ (10 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    simp at this
    linarith
  have h2 : (10 : ℝ) ^ ((4 : ℝ)) = 10000 := by norm_num
  linarith

/-- The statement of Lemma53Split.local_density, CONDITIONAL ON leaf_qres_count.
Each factor 1 - omega p / p is at least 1/2, which is at least p^(-1/10) for p at least 1024,
and the product of the primes of q is at most q. -/
theorem local_density_of_leaves (J w : ℕ) (hJ : 5 ≤ J) (hw : wBig ≤ w) (b : ℤ)
    (hb : Amenable (WW J w) b) (q Q' : ℕ) (hq : 1 ≤ q) (hQ' : Q'.Coprime q)
    (hqW : IsCoprime (q : ℤ) (WW J w)) :
    (q : ℝ) ^ ((9 : ℝ) / 10) ≤ #(QRes q (WW J w * Q') b) := by
  rw [leaf_qres_count J w hJ hw b hb q Q' hq hQ' hqW]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hw1024 : (1024 : ℝ) ≤ w := wBig_ge_1024.trans hw
  have hfac : ∀ p ∈ q.primeFactors,
      (p : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1 - (if p % 4 = 3 then (2 : ℝ) else 1) / p := by
    intro p hp
    have hpw : w < p := prime_factor_gt_w hJ hqW hp
    have hp1024 : (1024 : ℝ) ≤ p := hw1024.trans (by exact_mod_cast hpw.le)
    have hp0 : (0 : ℝ) < p := by linarith
    have h2 : (2 : ℝ) ≤ (p : ℝ) ^ (1 / 10 : ℝ) := by
      calc (2 : ℝ) = (1024 : ℝ) ^ (1 / 10 : ℝ) := by
            rw [show (1024 : ℝ) = 2 ^ (10 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
            norm_num
        _ ≤ (p : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_le_rpow (by norm_num) hp1024 (by norm_num)
    have hneg : (p : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1 / 2 := by
      rw [Real.rpow_neg hp0.le]
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      linarith
    have hω : (if p % 4 = 3 then (2 : ℝ) else 1) / p ≤ 1 / 2 := by
      rw [div_le_iff₀ hp0]
      split_ifs <;> linarith
    linarith
  have hprod : ∏ p ∈ q.primeFactors, (p : ℝ) ^ (-(1 / 10 : ℝ)) ≤
      ∏ p ∈ q.primeFactors, (1 - (if p % 4 = 3 then (2 : ℝ) else 1) / p) :=
    prod_le_prod₀ (fun p _ => by positivity) hfac
  have hpf : ∏ p ∈ q.primeFactors, (p : ℝ) ^ (-(1 / 10 : ℝ)) =
      ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ (-(1 / 10 : ℝ)) := by
    push_cast
    rw [Real.finset_prod_rpow _ _ (fun p _ => by positivity)]
  have hle : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
  have hpos : (0 : ℝ) < ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (prod_ne_zero_iff.mpr fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hmono : (q : ℝ) ^ (-(1 / 10 : ℝ)) ≤
      ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ (-(1 / 10 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)
  have hq910 : (q : ℝ) ^ ((9 : ℝ) / 10) = q * (q : ℝ) ^ (-(1 / 10 : ℝ)) := by
    rw [← Real.rpow_one_add' hq0.le (by norm_num)]
    norm_num
  rw [hq910]
  apply mul_le_mul_of_nonneg_left _ hq0.le
  rw [hpf] at hprod
  exact hmono.trans hprod

end LeanLab.Teravainen2016.Lemma53Split

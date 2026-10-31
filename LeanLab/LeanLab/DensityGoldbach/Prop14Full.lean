/-
P0038 Shao 2012, Proposition 1.4 for every odd squarefree m, from Propositions 3.1 and 3.2:
first m' 15 with m' coprime to 30 by CRT, averaging over the 15-fiber, Prop 3.1 mod m', then
Prop 3.2 mod 15; then down to 3 m' and 5 m' by pulling f back along a CRT projection.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0102Z-30056, unit U-0126.
-/
import LeanLab.DensityGoldbach.Prop31
import LeanLab.DensityGoldbach.Prop32

open Finset

namespace LeanLab.DensityGoldbach

lemma prop14_congr {m n : ℕ} (h : m = n) {_ : NeZero m} {_ : NeZero n} (hm : Prop14 m) :
    Prop14 n := by
  subst h; exact hm

/-- Prop 1.4 for `m' · 15`, `m'` with Prop 3.1 and coprime to `15`. -/
theorem prop14_mul15 (m : ℕ) [NeZero m] [NeZero (m * 15)] (hcop : m.Coprime 15)
    (hm : Prop31 m) : Prop14 (m * 15) := by
  intro f hf hsum x
  set e := ZMod.chineseRemainder hcop with he
  set F : ZMod m → ZMod 15 → ℝ := fun u v => f (e.symm (u, v)) with hF
  have h8 : (#(unitsMod 15) : ℝ) = 8 := by rw [P32.card_units15]; norm_num
  set f' : ZMod m → ℝ := fun u => (∑ v ∈ unitsMod 15, F u v) / 8 with hf'
  have hS : ∀ u, ∑ v ∈ unitsMod 15, F u v = 8 * f' u := by
    intro u; rw [hf']; ring
  have hf'bd : ∀ u, 0 ≤ f' u ∧ f' u ≤ 1 := by
    intro u
    have h0 : 0 ≤ ∑ v ∈ unitsMod 15, F u v := sum_nonneg fun v _ => (hf _).1
    have h1 : ∑ v ∈ unitsMod 15, F u v ≤ 8 := by
      calc ∑ v ∈ unitsMod 15, F u v ≤ ∑ v ∈ unitsMod 15, (1 : ℝ) :=
            sum_le_sum fun v _ => (hf _).2
        _ = 8 := by rw [sum_const, nsmul_one, h8]
    constructor
    · rw [hf']; positivity
    · rw [hf']; linarith
  have hsum' : 5 / 8 * (m.totient : ℝ) < ∑ u ∈ unitsMod m, f' u := by
    rw [sum_unitsMod_crt hcop, Nat.totient_mul hcop,
      show Nat.totient 15 = 8 by decide] at hsum
    have : ∑ u ∈ unitsMod m, ∑ v ∈ unitsMod 15, F u v = 8 * ∑ u ∈ unitsMod m, f' u := by
      rw [mul_sum]; exact sum_congr rfl fun u _ => hS u
    rw [this] at hsum
    push_cast at hsum
    linarith
  obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, hx1, hh⟩ := hm f' hf'bd hsum' (e x).1
  obtain ⟨s, hs, t, ht, r, hr, hx2, hprod, hsum3⟩ := shao_prop32 (F a₁) (F a₂) (F a₃)
    (fun v => hf _) (fun v => hf _) (fun v => hf _) (by
      rw [hS a₁, hS a₂, hS a₃]
      unfold hfun at hh
      nlinarith) (e x).2
  refine ⟨e.symm (a₁, s), ?_, e.symm (a₂, t), ?_, e.symm (a₃, r), ?_, ?_, hprod, hsum3⟩
  · rw [mem_unitsMod_crt hcop, RingEquiv.apply_symm_apply]; exact ⟨ha₁, hs⟩
  · rw [mem_unitsMod_crt hcop, RingEquiv.apply_symm_apply]; exact ⟨ha₂, ht⟩
  · rw [mem_unitsMod_crt hcop, RingEquiv.apply_symm_apply]; exact ⟨ha₃, hr⟩
  · apply e.injective
    rw [map_add, map_add, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, Prod.mk_add_mk, Prod.mk_add_mk, ← hx1, ← hx2]

/-- Descent: Prop 1.4 for `k e` with `k, e` coprime gives Prop 1.4 for `k`. -/
theorem prop14_of_mul (k n : ℕ) [NeZero k] [NeZero n] [NeZero (k * n)] (hcop : k.Coprime n)
    (h : Prop14 (k * n)) : Prop14 k := by
  intro f hf hsum x
  set e := ZMod.chineseRemainder hcop with he
  set g : ZMod (k * n) → ℝ := fun z => f (e z).1 with hg
  have hφ : (0 : ℝ) < (n.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  have hcard : (#(unitsMod n) : ℝ) = n.totient := by
    congr 1
    rw [unitsMod, ← ZMod.card_units_eq_totient, ← Fintype.card_coe]
    exact Fintype.card_congr
      { toFun := fun u => IsUnit.unit (mem_filter.1 u.2).2
        invFun := fun u => ⟨(u : ZMod n), mem_filter.2 ⟨mem_univ _, u.isUnit⟩⟩
        left_inv := fun u => by simp
        right_inv := fun u => by ext; simp }
  have hsumg : 5 / 8 * ((k * n).totient : ℝ) < ∑ z ∈ unitsMod (k * n), g z := by
    rw [sum_unitsMod_crt hcop, Nat.totient_mul hcop]
    have : ∀ u, ∑ v ∈ unitsMod n, g (e.symm (u, v)) = n.totient * f u := by
      intro u
      simp only [hg, RingEquiv.apply_symm_apply, sum_const, nsmul_eq_mul, hcard]
    rw [sum_congr rfl fun u _ => this u, ← mul_sum]
    push_cast
    nlinarith
  obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, hx, hprod, hs⟩ :=
    h g (fun z => hf _) hsumg (e.symm (x, 0))
  refine ⟨(e a₁).1, ((mem_unitsMod_crt hcop a₁).1 ha₁).1, (e a₂).1,
    ((mem_unitsMod_crt hcop a₂).1 ha₂).1, (e a₃).1, ((mem_unitsMod_crt hcop a₃).1 ha₃).1,
    ?_, hprod, hs⟩
  have := congrArg (fun z => (e z).1) hx
  simp only [RingEquiv.apply_symm_apply, map_add, Prod.fst_add] at this
  exact this

lemma coprime30_iff (m : ℕ) : m.Coprime 30 ↔ ¬ 2 ∣ m ∧ ¬ 3 ∣ m ∧ ¬ 5 ∣ m := by
  rw [show (30 : ℕ) = 2 * 3 * 5 from rfl, Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right,
    Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two, Nat.coprime_comm,
    Nat.Prime.coprime_iff_not_dvd Nat.prime_three, Nat.coprime_comm,
    Nat.Prime.coprime_iff_not_dvd Nat.prime_five, and_assoc]

lemma not_sq_dvd {m p : ℕ} (hsq : Squarefree m) (hp : p.Prime) (h : p * p ∣ m) : False :=
  hp.one_lt.ne' (Nat.isUnit_iff.1 (hsq p h))

/-- Prop 1.4 for `m' · 15`, `m' · 3` and `m' · 5`, `m'` squarefree and coprime to `30`. -/
theorem prop14_15 (m : ℕ) (hm0 : 0 < m) (hsq : Squarefree m) (h30 : m.Coprime 30) :
    ∀ (_ : NeZero (m * 15)), Prop14 (m * 15) := by
  intro _
  have : NeZero m := ⟨hm0.ne'⟩
  exact prop14_mul15 m (Nat.Coprime.coprime_dvd_right (by norm_num) h30) (prop31 m hsq h30)

theorem prop14_3 (m : ℕ) (hm0 : 0 < m) (hsq : Squarefree m) (h30 : m.Coprime 30) :
    ∀ (_ : NeZero (m * 3)), Prop14 (m * 3) := by
  intro _
  have : NeZero (m * 3 * 5) := ⟨by positivity⟩
  have : NeZero (m * 15) := ⟨by positivity⟩
  have hc : (m * 3).Coprime 5 := Nat.coprime_mul_iff_left.2
    ⟨Nat.Coprime.coprime_dvd_right (by norm_num) h30, by norm_num⟩
  exact prop14_of_mul (m * 3) 5 hc (prop14_congr (by ring) (prop14_15 m hm0 hsq h30 inferInstance))

theorem prop14_5 (m : ℕ) (hm0 : 0 < m) (hsq : Squarefree m) (h30 : m.Coprime 30) :
    ∀ (_ : NeZero (m * 5)), Prop14 (m * 5) := by
  intro _
  have : NeZero (m * 5 * 3) := ⟨by positivity⟩
  have : NeZero (m * 15) := ⟨by positivity⟩
  have hc : (m * 5).Coprime 3 := Nat.coprime_mul_iff_left.2
    ⟨Nat.Coprime.coprime_dvd_right (by norm_num) h30, by norm_num⟩
  exact prop14_of_mul (m * 5) 3 hc (prop14_congr (by ring) (prop14_15 m hm0 hsq h30 inferInstance))

/-- **Shao Proposition 1.4** in full: every odd squarefree `m`. -/
theorem prop_1_4_proved (m : ℕ) [NeZero m] (hodd : Odd m) (hsq : Squarefree m) : Prop14 m := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have h2 : ¬ 2 ∣ m := by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hodd
  by_cases h3 : 3 ∣ m <;> by_cases h5 : 5 ∣ m
  · obtain ⟨k, rfl⟩ : 15 ∣ m := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h5
    have hk0 : 0 < k := by omega
    have hk : k.Coprime 30 := by
      rw [coprime30_iff]
      refine ⟨fun h => h2 (dvd_mul_of_dvd_right h 15), fun h => ?_, fun h => ?_⟩
      · exact not_sq_dvd hsq Nat.prime_three (by
          obtain ⟨j, rfl⟩ := h; exact ⟨5 * j, by ring⟩)
      · exact not_sq_dvd hsq Nat.prime_five (by
          obtain ⟨j, rfl⟩ := h; exact ⟨3 * j, by ring⟩)
    have : NeZero (k * 15) := ⟨by positivity⟩
    exact prop14_congr (by ring) (prop14_15 k hk0 (hsq.squarefree_of_dvd (dvd_mul_left k 15)) hk
      inferInstance)
  · obtain ⟨k, rfl⟩ := h3
    have hk0 : 0 < k := by omega
    have hk : k.Coprime 30 := by
      rw [coprime30_iff]
      refine ⟨fun h => h2 (dvd_mul_of_dvd_right h 3), fun h => ?_,
        fun h => h5 (dvd_mul_of_dvd_right h 3)⟩
      exact not_sq_dvd hsq Nat.prime_three (mul_dvd_mul_left 3 h)
    have : NeZero (k * 3) := ⟨by positivity⟩
    exact prop14_congr (by ring) (prop14_3 k hk0 (hsq.squarefree_of_dvd (dvd_mul_left k 3)) hk
      inferInstance)
  · obtain ⟨k, rfl⟩ := h5
    have hk0 : 0 < k := by omega
    have hk : k.Coprime 30 := by
      rw [coprime30_iff]
      refine ⟨fun h => h2 (dvd_mul_of_dvd_right h 5), fun h => h3 (dvd_mul_of_dvd_right h 5),
        fun h => ?_⟩
      exact not_sq_dvd hsq Nat.prime_five (mul_dvd_mul_left 5 h)
    have : NeZero (k * 5) := ⟨by positivity⟩
    exact prop14_congr (by ring) (prop14_5 k hk0 (hsq.squarefree_of_dvd (dvd_mul_left k 5)) hk
      inferInstance)
  · exact prop14_coprime30 m hsq ((coprime30_iff m).2 ⟨h2, h3, h5⟩)

/-- **Shao Corollary 1.5** for every odd squarefree `m`. -/
theorem cor_1_5_proved (m : ℕ) [NeZero m] (hodd : Odd m) (hsq : Squarefree m) : Cor15 m :=
  cor15_of_prop14 m (prop_1_4_proved m hodd hsq)

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.prop_1_4_proved
#print axioms LeanLab.DensityGoldbach.cor_1_5_proved

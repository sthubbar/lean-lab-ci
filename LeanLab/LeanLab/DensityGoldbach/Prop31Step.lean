/-
P0038 Shao 2012, the induction step of Proposition 3.1: from modulus m to m p, p ≥ 11 prime
coprime to m, through the Chinese remainder theorem. Average f over the p-fiber, apply the
induction hypothesis mod m, then the fiber step `prime_three` mod p.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0102Z-30056, unit U-0111.
-/
import LeanLab.DensityGoldbach.Prop31Prime

open Finset

namespace LeanLab.DensityGoldbach

lemma mem_unitsMod {m : ℕ} [NeZero m] (z : ZMod m) : z ∈ unitsMod m ↔ IsUnit z := by
  simp [unitsMod]

/-- Reduced residues mod `m p` are the pairs of reduced residues, through CRT. -/
lemma mem_unitsMod_crt {m p : ℕ} [NeZero m] [NeZero p] [NeZero (m * p)] (hcop : m.Coprime p)
    (z : ZMod (m * p)) : z ∈ unitsMod (m * p) ↔
      (ZMod.chineseRemainder hcop z).1 ∈ unitsMod m ∧
        (ZMod.chineseRemainder hcop z).2 ∈ unitsMod p := by
  rw [mem_unitsMod, mem_unitsMod, mem_unitsMod, ← Prod.isUnit_iff]
  exact (MulEquiv.isUnit_map (ZMod.chineseRemainder hcop)).symm

/-- The sum over reduced residues mod `m p` as a double sum. -/
lemma sum_unitsMod_crt {m p : ℕ} [NeZero m] [NeZero p] [NeZero (m * p)] (hcop : m.Coprime p)
    (f : ZMod (m * p) → ℝ) : ∑ z ∈ unitsMod (m * p), f z =
      ∑ u ∈ unitsMod m, ∑ v ∈ unitsMod p, f ((ZMod.chineseRemainder hcop).symm (u, v)) := by
  set e := ZMod.chineseRemainder hcop
  rw [← sum_product (unitsMod m) (unitsMod p)
    (fun q : ZMod m × ZMod p => f (e.symm q))]
  refine sum_nbij' (fun z => e z) (fun q => e.symm q) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rw [mem_product]
    exact (mem_unitsMod_crt hcop z).1 hz
  · intro q hq
    rw [mem_product] at hq
    rw [mem_unitsMod_crt hcop, RingEquiv.apply_symm_apply]
    exact hq
  · intro z _; simp
  · intro q _; simp
  · intro z _; simp

/-- **Shao Prop 3.1, induction step**: `Prop31 m` gives `Prop31 (m p)` for a prime `p ≥ 11`
coprime to `m`. -/
theorem prop31_step (m p : ℕ) [NeZero m] [hp : Fact p.Prime] [NeZero (m * p)] (hp11 : 11 ≤ p)
    (hcop : m.Coprime p) (hm : Prop31 m) : Prop31 (m * p) := by
  intro f hf hsum x
  have : NeZero p := ⟨hp.out.ne_zero⟩
  set e := ZMod.chineseRemainder hcop with he
  set F : ZMod m → ZMod p → ℝ := fun u v => f (e.symm (u, v)) with hF
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (11 : ℝ) ≤ p := by exact_mod_cast hp11
    linarith
  have hcardp : (#(unitsMod p) : ℝ) = (p : ℝ) - 1 := by
    rw [card_unitsMod_prime p, Nat.cast_sub hp.out.one_le, Nat.cast_one]
  -- the averaged function mod `m`
  set f' : ZMod m → ℝ := fun u => (∑ v ∈ unitsMod p, F u v) / ((p : ℝ) - 1) with hf'
  have hS : ∀ u, ∑ v ∈ unitsMod p, F u v = ((p : ℝ) - 1) * f' u := by
    intro u; rw [hf']; field_simp
  have hf'bd : ∀ u, 0 ≤ f' u ∧ f' u ≤ 1 := by
    intro u
    have h0 : 0 ≤ ∑ v ∈ unitsMod p, F u v := sum_nonneg fun v _ => (hf _).1
    have h1 : ∑ v ∈ unitsMod p, F u v ≤ (p : ℝ) - 1 := by
      calc ∑ v ∈ unitsMod p, F u v ≤ ∑ v ∈ unitsMod p, (1 : ℝ) :=
            sum_le_sum fun v _ => (hf _).2
        _ = (p : ℝ) - 1 := by rw [sum_const, nsmul_one, hcardp]
    constructor
    · exact div_nonneg h0 hp1.le
    · rw [div_le_one hp1]; exact h1
  have hsum' : 5 / 8 * (m.totient : ℝ) < ∑ u ∈ unitsMod m, f' u := by
    rw [sum_unitsMod_crt hcop, Nat.totient_mul hcop, Nat.totient_prime hp.out] at hsum
    have : ∑ u ∈ unitsMod m, ∑ v ∈ unitsMod p, F u v =
        ((p : ℝ) - 1) * ∑ u ∈ unitsMod m, f' u := by
      rw [mul_sum]; exact sum_congr rfl fun u _ => hS u
    rw [this] at hsum
    push_cast at hsum
    rw [Nat.cast_sub hp.out.one_le, Nat.cast_one] at hsum
    nlinarith
  obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, hx1, hh⟩ := hm f' hf'bd hsum' (e x).1
  have hpos := prime_three p hp11 (F a₁) (F a₂) (F a₃) (fun v => hf _) (fun v => hf _)
    (fun v => hf _) (by
      rw [hS a₁, hS a₂, hS a₃]
      unfold hfun at hh
      have hq : 0 < ((p : ℝ) - 1) ^ 2 := by positivity
      nlinarith [mul_lt_mul_of_pos_left hh hq]) (e x).2
  obtain ⟨s, hs, t, ht, r, hr, hx2, hh2⟩ := hpos
  refine ⟨e.symm (a₁, s), ?_, e.symm (a₂, t), ?_, e.symm (a₃, r), ?_, ?_, hh2⟩
  · rw [mem_unitsMod_crt hcop, RingEquiv.apply_symm_apply]; exact ⟨ha₁, hs⟩
  · rw [mem_unitsMod_crt hcop, RingEquiv.apply_symm_apply]; exact ⟨ha₂, ht⟩
  · rw [mem_unitsMod_crt hcop, RingEquiv.apply_symm_apply]; exact ⟨ha₃, hr⟩
  · apply e.injective
    rw [map_add, map_add, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, Prod.mk_add_mk, Prod.mk_add_mk, ← hx1, ← hx2]

end LeanLab.DensityGoldbach

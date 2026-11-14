/-
Gallagher 1975 p.134 Lemma 5. General base residue counts.
Source https://doi.org/10.1007/BF01390190
The proof extends the existing base two argument in Romanov.Residues134.
It uses Mathlib unit powers and finite cardinality injections.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib
namespace LeanLab.Linnik.Decomp554c
open Finset
/-- Gallagher page 134, fixing a residue fixes the exponent modulo the order. -/
theorem pow_residue_count_le_nat (g q : ℕ) (hgq : Nat.Coprime g q) (c L : ℕ) :
    #{μ ∈ Icc 1 L | g ^ μ % q = c} ≤ L / orderOf (g : ZMod q) + 1 := by
  classical
  calc
    #{μ ∈ Icc 1 L | g ^ μ % q = c} ≤ #(range (L / orderOf (g : ZMod q) + 1)) := by
      apply card_le_card_of_injOn (fun μ => μ / orderOf (g : ZMod q))
      · intro μ hμ
        simp only [mem_coe, mem_filter, mem_Icc] at hμ
        rw [mem_coe, mem_range]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right hμ.1.2)
      · intro a ha b hb hab
        simp only [mem_coe, mem_filter, mem_Icc] at ha hb
        change a / orderOf (g : ZMod q) = b / orderOf (g : ZMod q) at hab
        have hpow : g ^ a ≡ g ^ b [MOD q] := by
          change g ^ a % q = g ^ b % q
          exact ha.2.trans hb.2.symm
        have hu : IsUnit (g : ZMod q) :=
          (ZMod.isUnit_iff_coprime g q).mpr hgq
        have heq : (g : ZMod q) ^ a = (g : ZMod q) ^ b := by
          simpa only [Nat.cast_pow] using
            (ZMod.natCast_eq_natCast_iff _ _ _).mpr hpow
        have hequ : hu.unit ^ a = hu.unit ^ b := Units.ext heq
        have hmod := pow_eq_pow_iff_modEq.mp hequ
        have hord : orderOf (g : ZMod q) = orderOf hu.unit := @orderOf_units (ZMod q) _ hu.unit
        rw [← hord] at hmod
        change a % orderOf (g : ZMod q) = b % orderOf (g : ZMod q) at hmod
        calc a = a % orderOf (g : ZMod q) + orderOf (g : ZMod q) * (a / orderOf (g : ZMod q)) := (Nat.mod_add_div a _).symm
          _ = b % orderOf (g : ZMod q) + orderOf (g : ZMod q) * (b / orderOf (g : ZMod q)) := by rw [hmod, hab]
          _ = b := Nat.mod_add_div b _
    _ = _ := card_range _

/-- Gallagher page 134, the real valued form of the one variable residue bound. -/
theorem pow_residue_count_le (g q : ℕ) (hgq : Nat.Coprime g q) (c L : ℕ) :
    (#{μ ∈ Icc 1 L | g ^ μ % q = c} : ℝ) ≤
      (L : ℝ) / orderOf (g : ZMod q) + 1 := by
  calc
    (#{μ ∈ Icc 1 L | g ^ μ % q = c} : ℝ) ≤
        ((L / orderOf (g : ZMod q) + 1 : ℕ) : ℝ) := by
      exact_mod_cast pow_residue_count_le_nat g q hgq c L
    _ ≤ _ := by
      push_cast
      exact add_le_add Nat.cast_div_le le_rfl

/-- Gallagher page 134, fix every exponent except the first. Tuples are counted with multiplicity. -/
theorem tuple_residue_count_le_nat (g q : ℕ) (hgq : Nat.Coprime g q) (K L c : ℕ) :
    #{ν : Fin (K + 1) → Fin L | (∑ i, g ^ ((ν i : ℕ) + 1)) % q = c} ≤
      L ^ K * (L / orderOf (g : ZMod q) + 1) := by
  classical
  let E := orderOf (g : ZMod q)
  have hsplit (ν : Fin (K + 1) → Fin L) :
      (∑ i, g ^ ((ν i : ℕ) + 1)) = g ^ ((ν 0 : ℕ) + 1) + (∑ i, g ^ ((Fin.tail ν i : ℕ) + 1)) := by
    exact Fin.sum_univ_succ _
  calc
    #{ν : Fin (K + 1) → Fin L | (∑ i, g ^ ((ν i : ℕ) + 1)) % q = c} ≤
        #((univ : Finset (Fin K → Fin L)) ×ˢ range (L / E + 1)) := by
      apply card_le_card_of_injOn (fun ν : Fin (K + 1) → Fin L =>
        (Fin.tail ν, ((ν 0 : ℕ) + 1) / E))
      · intro ν hν
        simp only [mem_coe, mem_product, mem_univ, true_and, mem_range]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right (by have := (ν 0).isLt; omega))
      · intro a ha b hb hab
        have ht : Fin.tail a = Fin.tail b := congrArg Prod.fst hab
        have hd : ((a 0 : ℕ) + 1) / E = ((b 0 : ℕ) + 1) / E := congrArg Prod.snd hab
        have ha' := (mem_filter.mp ha).2
        have hb' := (mem_filter.mp hb).2
        have hsum : (∑ i, g ^ ((a i : ℕ) + 1)) ≡ (∑ i, g ^ ((b i : ℕ) + 1)) [MOD q] := ha'.trans hb'.symm
        rw [hsplit a, hsplit b, ht] at hsum
        have hpow := Nat.ModEq.add_right_cancel' ((∑ i, g ^ ((Fin.tail b i : ℕ) + 1))) hsum
        have hu : IsUnit (g : ZMod q) :=
          (ZMod.isUnit_iff_coprime g q).mpr hgq
        have heq : (g : ZMod q) ^ ((a 0 : ℕ) + 1) = (g : ZMod q) ^ ((b 0 : ℕ) + 1) := by
          simpa only [Nat.cast_pow] using
            (ZMod.natCast_eq_natCast_iff _ _ _).mpr hpow
        have hequ : hu.unit ^ ((a 0 : ℕ) + 1) = hu.unit ^ ((b 0 : ℕ) + 1) := Units.ext heq
        have hmod := pow_eq_pow_iff_modEq.mp hequ
        have hord : E = orderOf hu.unit := @orderOf_units (ZMod q) _ hu.unit
        rw [← hord] at hmod
        change ((a 0 : ℕ) + 1) % E = ((b 0 : ℕ) + 1) % E at hmod
        have hfirst : a 0 = b 0 := by
          apply Fin.ext
          have haa := Nat.mod_add_div ((a 0 : ℕ) + 1) E
          have hbb := Nat.mod_add_div ((b 0 : ℕ) + 1) E
          rw [hmod, hd] at haa
          omega
        funext i
        exact Fin.cases hfirst (fun j => congrFun ht j) i
    _ = _ := by simp [E]

/-- Gallagher page 134, the real bound after fixing every other exponent. -/
theorem tuple_residue_count_le (g q : ℕ) (hgq : Nat.Coprime g q) (K L c : ℕ) :
    (#{ν : Fin (K + 1) → Fin L | (∑ i, g ^ ((ν i : ℕ) + 1)) % q = c} : ℝ) ≤
      (L : ℝ) ^ (K + 1) / orderOf (g : ZMod q) + (L : ℝ) ^ K := by
  have h : (#{ν : Fin (K + 1) → Fin L | (∑ i, g ^ ((ν i : ℕ) + 1)) % q = c} : ℝ) ≤
      (L : ℝ) ^ K * (((L / orderOf (g : ZMod q) : ℕ) : ℝ) + 1) := by
    exact_mod_cast tuple_residue_count_le_nat g q hgq K L c
  calc
    (#{ν : Fin (K + 1) → Fin L | (∑ i, g ^ ((ν i : ℕ) + 1)) % q = c} : ℝ) ≤
        (L : ℝ) ^ K * (((L / orderOf (g : ZMod q) : ℕ) : ℝ) + 1) := h
    _ ≤ (L : ℝ) ^ K * ((L : ℝ) / orderOf (g : ZMod q) + 1) :=
      mul_le_mul_of_nonneg_left (add_le_add Nat.cast_div_le le_rfl) (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- Gallagher 1975 p.134 Lemma 5 display 5 for every base coprime to q.
Fixing all but one exponent leaves at most one exponent in each order period. -/
theorem pair_congruence_count_le (g q : ℕ) (hgq : Nat.Coprime g q)
    (k L : ℕ) (hk : 2 ≤ k) :
    (((Finset.univ : Finset ((Fin k → Fin L) × (Fin k → Fin L))).filter
      (fun x => Nat.ModEq q (∑ i, g ^ ((x.1 i : ℕ) + 1))
        (∑ i, g ^ ((x.2 i : ℕ) + 1)))).card : ℝ) ≤
      (L : ℝ) ^ (2 * k) / orderOf (g : ZMod q) + (L : ℝ) ^ (2 * k - 1) := by
  classical
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  let A := Fin (K + 1) → Fin L
  let S : Finset (A × A) := Finset.univ.filter (fun x =>
    Nat.ModEq q (∑ i, g ^ ((x.1 i : ℕ) + 1)) (∑ i, g ^ ((x.2 i : ℕ) + 1)))
  let E := orderOf (g : ZMod q)
  have hfiber (ν : A) :
      (S.filter (fun x => x.1 = ν)).card ≤ L ^ K * (L / E + 1) := by
    let T : Finset A := Finset.univ.filter (fun μ =>
      (∑ i, g ^ ((μ i : ℕ) + 1)) % q = (∑ i, g ^ ((ν i : ℕ) + 1)) % q)
    have hmap : (S.filter (fun x => x.1 = ν)).card ≤ T.card := by
      apply Finset.card_le_card_of_injOn Prod.snd
      · intro x hx
        rcases Finset.mem_filter.mp hx with ⟨hx, hν⟩
        have h := (Finset.mem_filter.mp hx).2
        rw [hν] at h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.symm⟩
      · intro x hx y hy heq
        have hxν := (Finset.mem_filter.mp hx).2
        have hyν := (Finset.mem_filter.mp hy).2
        exact Prod.ext (hxν.trans hyν.symm) heq
    exact hmap.trans (tuple_residue_count_le_nat g q hgq K L _)
  have hn := Finset.card_le_mul_card_image_of_maps_to
    (f := Prod.fst) (s := S) (t := (Finset.univ : Finset A))
    (fun _ _ => Finset.mem_univ _) (L ^ K * (L / E + 1)) (fun ν _ => hfiber ν)
  have hnat : S.card ≤ L ^ (K + 1) * L ^ K * (L / E + 1) := by
    simpa [A, mul_assoc, mul_comm, mul_left_comm] using hn
  have hr : (S.card : ℝ) ≤ (L : ℝ) ^ (K + 1) * (L : ℝ) ^ K *
      (((L / E : ℕ) : ℝ) + 1) := by exact_mod_cast hnat
  change (S.card : ℝ) ≤ _
  calc
    _ ≤ (L : ℝ) ^ (K + 1) * (L : ℝ) ^ K * (((L / E : ℕ) : ℝ) + 1) := hr
    _ ≤ (L : ℝ) ^ (K + 1) * (L : ℝ) ^ K * ((L : ℝ) / E + 1) :=
      mul_le_mul_of_nonneg_left (add_le_add Nat.cast_div_le le_rfl) (by positivity)
    _ = _ := by
      rw [← pow_add, show 2 * (K + 1) - 1 = K + 1 + K by omega,
        show 2 * (K + 1) = (K + 1 + K) + 1 by omega, pow_succ]
      dsimp [E]
      ring

end LeanLab.Linnik.Decomp554c

#print axioms LeanLab.Linnik.Decomp554c.pow_residue_count_le_nat

#print axioms LeanLab.Linnik.Decomp554c.pow_residue_count_le

#print axioms LeanLab.Linnik.Decomp554c.tuple_residue_count_le_nat

#print axioms LeanLab.Linnik.Decomp554c.tuple_residue_count_le

#print axioms LeanLab.Linnik.Decomp554c.pair_congruence_count_le

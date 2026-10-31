/-
P0006 page 3, Section 4. Exact residue counts underlying the one half
heuristic. Theorems here count finite field residues. They do not assert
independence for the paper's sampled primes. AI wrote the Lean code.
Binary Goldbach is open.
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace LeanLab.HelfgottPlatt.Task133

/-- Page 3, the standard finite field fact behind the one half witness
heuristic. Exactly half of the nonzero field elements have quadratic
character one. This counts residues, not sampled prime candidates. -/
theorem quadraticChar_half {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2) :
    2 * ((Finset.univ : Finset F).filter (fun x => quadraticChar F x = 1)).card + 1 =
      Fintype.card F := by
  classical
  have hpoint (x : F) :
      (if quadraticChar F x = 1 then (2 : ℤ) else 0) +
        (if x = 0 then 1 else 0) = 1 + quadraticChar F x := by
    by_cases hx : x = 0
    · simp [hx]
    · rcases quadraticChar_dichotomy hx with h | h <;> simp [hx, h]
  have hs :
      (∑ x : F, ((if quadraticChar F x = 1 then (2 : ℤ) else 0) +
        (if x = 0 then 1 else 0))) = Fintype.card F := by
    calc
      _ = ∑ x : F, (1 + quadraticChar F x) := Finset.sum_congr rfl (fun x _ => hpoint x)
      _ = Fintype.card F := by rw [Finset.sum_add_distrib, quadraticChar_sum_zero hF]; simp
  have htwo (x : F) :
      (if quadraticChar F x = 1 then (2 : ℤ) else 0) =
        2 * (if quadraticChar F x = 1 then 1 else 0) := by split_ifs <;> norm_num
  simp_rw [htwo] at hs
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  simp only [Finset.sum_boole] at hs
  have hz : ((Finset.univ : Finset F).filter (fun x => x = 0)).card = 1  := by
    have he : (Finset.univ : Finset F).filter (fun x => x = 0) = {0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [he, Finset.card_singleton]
  rw [hz] at hs
  exact_mod_cast hs

/-- Page 3, the one half residue calculation in subtype form. -/
theorem quadraticChar_one_card {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) :
    Nat.card {x : F // quadraticChar F x = 1} = (Fintype.card F - 1) / 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h := quadraticChar_half hF
  omega

/-- Page 3, the one half heuristic at an odd prime witness modulus.
Exactly half of its nonzero residues have Jacobi symbol one. -/
theorem jacobi_one_card {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card {x : ZMod p // jacobiSym x.val p = 1} = (p - 1) / 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have he (x : ZMod p) : jacobiSym x.val p = quadraticChar (ZMod p) x := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym]
    simp
  calc
    _ = Nat.card {x : ZMod p // quadraticChar (ZMod p) x = 1} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [he]))
    _ = (p - 1) / 2 := by
      simpa only [ZMod.card] using quadraticChar_one_card (F := ZMod p)
        (by simpa only [ZMod.ringChar_zmod_n] using hp2)

/-- Page 3, independent residue interpretation of the one half heuristic.
CRT makes simultaneous Jacobi-one conditions at distinct odd prime moduli
an exact product count. This is not a prime sampling theorem. -/
theorem crt_jacobi_one_card {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hodd : ∀ i, p i ≠ 2)
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) :
    Nat.card {x : ZMod (∏ i, p i) //
      ∀ i, jacobiSym ((ZMod.prodEquivPi p hc) x i).val (p i) = 1} =
      ∏ i, (p i - 1) / 2 := by
  classical
  calc
    _ = Nat.card (∀ i, {x : ZMod (p i) // jacobiSym x.val (p i) = 1}) := by
      apply Nat.card_congr
      exact (Equiv.subtypeEquivOfSubtype
        (p := fun f : ∀ i, ZMod (p i) => ∀ i, jacobiSym (f i).val (p i) = 1)
        (ZMod.prodEquivPi p hc).toEquiv).trans
          (Equiv.subtypePiEquivPi (p := fun i (x : ZMod (p i)) => jacobiSym x.val (p i) = 1))
    _ = ∏ i, Nat.card {x : ZMod (p i) // jacobiSym x.val (p i) = 1} := Nat.card_pi
    _ = ∏ i, (p i - 1) / 2 :=
      Finset.prod_congr rfl (fun i _ => jacobi_one_card (hp i) (hodd i))

/-- Page 3, the population for the independent residue comparison. CRT
counts the residues nonzero at each modulus by a product. -/
theorem crt_nonzero_card {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hp : ∀ i, 0 < p i) (hc : Pairwise (fun i j => (p i).Coprime (p j))) :
    Nat.card {x : ZMod (∏ i, p i) // ∀ i, (ZMod.prodEquivPi p hc) x i ≠ 0} =
      ∏ i, (p i - 1) := by
  classical
  letI : ∀ i, NeZero (p i) := fun i => ⟨(hp i).ne'⟩
  calc
    _ = Nat.card (∀ i, {x : ZMod (p i) // x ≠ 0}) := by
      apply Nat.card_congr
      exact (Equiv.subtypeEquivOfSubtype
        (p := fun f : ∀ i, ZMod (p i) => ∀ i, f i ≠ 0)
        (ZMod.prodEquivPi p hc).toEquiv).trans
          (Equiv.subtypePiEquivPi (p := fun i (x : ZMod (p i)) => x ≠ 0))
    _ = ∏ i, Nat.card {x : ZMod (p i) // x ≠ 0} := Nat.card_pi
    _ = ∏ i, (p i - 1) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
        Fintype.card_subtype_eq, ZMod.card]

/-- Page 3, exact ratio for independent nonzero residues at odd prime
moduli. One simultaneous Jacobi-one tuple occurs for every two to the
number of moduli among the nonzero tuples. -/
theorem crt_residue_ratio {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hodd : ∀ i, p i ≠ 2)
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) :
    2 ^ Fintype.card ι * Nat.card {x : ZMod (∏ i, p i) //
      ∀ i, jacobiSym ((ZMod.prodEquivPi p hc) x i).val (p i) = 1} =
      Nat.card {x : ZMod (∏ i, p i) // ∀ i, (ZMod.prodEquivPi p hc) x i ≠ 0} := by
  rw [crt_jacobi_one_card p hp hodd hc, crt_nonzero_card p (fun i => (hp i).pos) hc]
  calc
    _ = ∏ i, (2 * ((p i - 1) / 2)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    _ = ∏ i, (p i - 1) := by
      apply Finset.prod_congr rfl
      intro i _
      obtain ⟨a, ha⟩ := (hp i).odd_of_ne_two (hodd i)
      omega

/-- Page 3, the exact independent residue count written on the canonical
natural representative, without explicit CRT projections in the predicate. -/
theorem crt_jacobi_one_val_card {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hodd : ∀ i, p i ≠ 2)
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) :
    Nat.card {x : ZMod (∏ i, p i) // ∀ i, jacobiSym x.val (p i) = 1} =
      ∏ i, (p i - 1) / 2 := by
  classical
  have : ∀ i, NeZero (p i) := fun i => ⟨(hp i).ne_zero⟩
  have hprod : 0 < ∏ i, p i := Finset.prod_pos (fun i _ => (hp i).pos)
  have : NeZero (∏ i, p i) := ⟨hprod.ne'⟩
  have he (x : ZMod (∏ i, p i)) (i : ι) :
      jacobiSym ((ZMod.prodEquivPi p hc) x i).val (p i) = jacobiSym x.val (p i) := by
    rw [ZMod.prodEquivPi_apply, ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.val_natCast]
    simpa only [Int.natCast_mod] using (jacobiSym.mod_left (x.val : ℤ) (p i)).symm
  calc
    _ = Nat.card {x : ZMod (∏ i, p i) //
        ∀ i, jacobiSym ((ZMod.prodEquivPi p hc) x i).val (p i) = 1} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => by simp only [he]))
    _ = ∏ i, (p i - 1) / 2 := crt_jacobi_one_card p hp hodd hc

/-- Page 3, the independent nonzero population on canonical natural
representatives. Each small modulus excludes exactly its zero residue. -/
theorem crt_nonzero_val_card {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hp : ∀ i, 0 < p i) (hc : Pairwise (fun i j => (p i).Coprime (p j))) :
    Nat.card {x : ZMod (∏ i, p i) // ∀ i, (x.val : ZMod (p i)) ≠ 0} =
      ∏ i, (p i - 1) := by
  classical
  have hprod : 0 < ∏ i, p i := Finset.prod_pos (fun i _ => hp i)
  have : NeZero (∏ i, p i) := ⟨hprod.ne'⟩
  have he (x : ZMod (∏ i, p i)) (i : ι) :
      (ZMod.prodEquivPi p hc) x i = (x.val : ZMod (p i)) := by
    rw [ZMod.prodEquivPi_apply, ZMod.castHom_apply, ZMod.natCast_val]
  calc
    _ = Nat.card {x : ZMod (∏ i, p i) // ∀ i, (ZMod.prodEquivPi p hc) x i ≠ 0} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => by simp only [he]))
    _ = ∏ i, (p i - 1) := crt_nonzero_card p hp hc

end LeanLab.HelfgottPlatt.Task133

import LeanLab.OpenProblems.Erdos273

/-!
# Tree certificates for covering systems

AI wrote the Lean code. This is target infrastructure for Erdos 273.
It proves no open problem. Goldbach remains OPEN.

The checker tracks a residue `a` modulo `d`. At a split it refines that class
by a prime power `q`, using every residue `a + d*r` modulo `d*q`.
A leaf names a pair in `S`. Its modulus must divide `d`, and its class must
contain `a`. Thus the entire tracked class lies in that named class.
The root is the class zero modulo one, which contains every integer.

Source: the task282 tree specification and the covering definition at
https://www.erdosproblems.com/273. This construction is elementary infrastructure.
There is no paper page asserting this particular checker.
-/

namespace LeanLab.OpenProblems.Erdos273

/-- Certificate data. A split has one child for each residue of a prime power. -/
inductive CoverTree where
  | leaf (s : ℕ × ℤ)
  | split (p k : ℕ) (children : Fin (p ^ k) → CoverTree)

/-- Check a tree for the class `a` modulo `d`, inside a common multiple `M`.
Every split uses a new prime power factor of `M`. Leaves name actual classes of `S`. -/
def checkTree (S : Finset (ℕ × ℤ)) (M d : ℕ) (a : ℤ) : CoverTree → Bool
  | .leaf s => decide (s ∈ S ∧ (s.1 : ℤ) ∣ (d : ℤ) ∧ (s.1 : ℤ) ∣ a - s.2)
  | .split p k children =>
      decide (p.Prime ∧ 0 < k ∧ Nat.Coprime d (p ^ k) ∧ d * p ^ k ∣ M) &&
        (List.finRange (p ^ k)).all fun r =>
          checkTree S M (d * p ^ k) (a + (d : ℤ) * r.val) (children r)

/-- Every integer in a class modulo `d` lies in one of its `q` refinements. -/
theorem exists_refined_class {d q : ℕ} (hq : 0 < q) {a x : ℤ}
    (hx : (d : ℤ) ∣ x - a) :
    ∃ r : Fin q, ((d * q : ℕ) : ℤ) ∣ x - (a + (d : ℤ) * r.val) := by
  obtain ⟨z, hz⟩ := hx
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hr0 : 0 ≤ z % (q : ℤ) := Int.emod_nonneg _ hq'.ne'
  have hr1 : z % (q : ℤ) < q := Int.emod_lt_of_pos _ hq'
  refine ⟨⟨(z % (q : ℤ)).toNat, by omega⟩, z / q, ?_⟩
  simp only [Nat.cast_mul, Int.toNat_of_nonneg hr0]
  have he := Int.emod_add_mul_ediv z q
  calc
    x - (a + (d : ℤ) * (z % (q : ℤ))) = (d : ℤ) * (z - z % (q : ℤ)) := by
      linear_combination hz
    _ = ((d : ℤ) * q) * (z / q) := by
      rw [show z - z % (q : ℤ) = (q : ℤ) * (z / q) by omega]
      ring

/-- A checked subtree covers every integer in its tracked residue class. -/
theorem checkTree_sound (t : CoverTree) {S : Finset (ℕ × ℤ)} {M d : ℕ} {a : ℤ}
    (h : checkTree S M d a t = true) :
    ∀ x : ℤ, (d : ℤ) ∣ x - a → ∃ s ∈ S, (s.1 : ℤ) ∣ x - s.2 := by
  induction t generalizing d a with
  | leaf s =>
      simp only [checkTree, decide_eq_true_eq] at h
      intro x hx
      refine ⟨s, h.1, ?_⟩
      have hd := dvd_add (h.2.1.trans hx) h.2.2
      convert hd using 1; ring
  | split p k children ih =>
      simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true] at h
      intro x hx
      have hq : 0 < p ^ k := pow_pos h.1.1.pos k
      obtain ⟨r, hr⟩ := exists_refined_class hq hx
      exact ih r (h.2 r (List.mem_finRange r)) x hr

/-- A successful root check proves the sealed covering predicate. -/
theorem covers_of_tree {S : Finset (ℕ × ℤ)} {M : ℕ} {t : CoverTree}
    (h : checkTree S M 1 0 t = true) : Covers S := by
  intro x
  exact checkTree_sound t h x (by simp)

/-- An adaptive certificate for the sealed Selfridge system. -/
def selfridgeTree : CoverTree :=
  .split 2 3 (fun r => match r.val with
      | 0 => .leaf (2, 0)
      | 1 => .leaf (4, 1)
      | 2 => .leaf (2, 0)
      | 3 => .split 3 2 (fun r => match r.val with
        | 0 => .leaf (6, 3)
        | 1 => .leaf (12, 11)
        | 2 => .leaf (18, 1)
        | 3 => .leaf (6, 3)
        | 4 => .leaf (12, 11)
        | 5 => .leaf (36, 7)
        | 6 => .leaf (6, 3)
        | 7 => .leaf (12, 11)
        | _ => .leaf (72, 67))
      | 4 => .leaf (2, 0)
      | 5 => .leaf (4, 1)
      | 6 => .leaf (2, 0)
      | _ => .split 3 2 (fun r => match r.val with
        | 0 => .leaf (36, 7)
        | 1 => .leaf (6, 3)
        | 2 => .leaf (12, 11)
        | 3 => .split 5 1 (fun r => match r.val with
          | 0 => .leaf (30, 1)
          | 1 => .leaf (40, 23)
          | 2 => .leaf (180, 175)
          | 3 => .leaf (10, 7)
          | _ => .leaf (60, 19))
        | 4 => .leaf (6, 3)
        | 5 => .leaf (12, 11)
        | 6 => .leaf (18, 1)
        | 7 => .leaf (6, 3)
        | _ => .leaf (12, 11)))

/-- The tree checker accepts the Selfridge certificate by kernel computation. -/
theorem check_selfridge_tree : checkTree selfridge 360 1 0 selfridgeTree = true := by
  decide +kernel

/-- The accepted tree proves the original infinite covering statement. -/
theorem covers_selfridge_tree : Covers selfridge := covers_of_tree check_selfridge_tree

/-- The same tree rejects the single even residue class. -/
theorem check_single_pair_false : checkTree {(2, 0)} 360 1 0 selfridgeTree = false := by
  decide +kernel

/-- A covering passes the original finite checker on every finite range. -/
theorem checkCover_of_covers {L : List (ℕ × ℤ)} (h : Covers L.toFinset) (M : ℕ) :
    checkCover M L = true := by
  simp only [checkCover, List.all_eq_true, List.any_eq_true, decide_eq_true_eq]
  intro r _
  obtain ⟨s, hs, hd⟩ := h r
  exact ⟨s, List.mem_toFinset.mp hs, Int.emod_eq_zero_of_dvd hd⟩

/-- An accepted tree also supplies the original checkCover conclusion. -/
theorem checkCover_of_tree {L : List (ℕ × ℤ)} {M : ℕ} {t : CoverTree}
    (h : checkTree L.toFinset M 1 0 t = true) : checkCover M L = true :=
  checkCover_of_covers (covers_of_tree h) M

/-- No tree can certify the single even residue class. -/
theorem checkTree_single_pair_false (M : ℕ) (t : CoverTree) :
    checkTree {(2, 0)} M 1 0 t = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨s, hs, hd⟩ := covers_of_tree h 1
  simp only [Finset.mem_singleton] at hs
  subst s
  norm_num at hd

/-- Completeness for supplied pairwise coprime prime power factors.
The factors need no search over all residues in the soundness proof. -/
theorem exists_tree_of_factors {S : Finset (ℕ × ℤ)} (hS : Covers S) (factors : List ℕ)
    (hpow : ∀ q ∈ factors, ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ q = p ^ k)
    (hpair : factors.Pairwise Nat.Coprime) {M d : ℕ}
    (hcop : ∀ q ∈ factors, Nat.Coprime d q) (hM : d * factors.prod ∣ M)
    (hmod : ∀ s ∈ S, s.1 ∣ d * factors.prod) (a : ℤ) :
    ∃ t : CoverTree, checkTree S M d a t = true := by
  classical
  induction factors generalizing d a with
  | nil =>
      obtain ⟨s, hs, ha⟩ := hS a
      have hd : (s.1 : ℤ) ∣ (d : ℤ) :=
        Int.natCast_dvd_natCast.mpr (by simpa using hmod s hs)
      exact ⟨.leaf s, by simpa only [checkTree, decide_eq_true_eq] using ⟨hs, hd, ha⟩⟩
  | cons q rest ih =>
      obtain ⟨p, k, hp, hk, rfl⟩ := hpow q (List.mem_cons_self ..)
      have hpairs := List.pairwise_cons.mp hpair
      have hM' : (d * p ^ k) * rest.prod ∣ M := by
        simpa only [List.prod_cons, Nat.mul_assoc] using hM
      have hmod' : ∀ s ∈ S, s.1 ∣ (d * p ^ k) * rest.prod := by
        simpa only [List.prod_cons, Nat.mul_assoc] using hmod
      have hcop' : ∀ q ∈ rest, Nat.Coprime (d * p ^ k) q := by
        intro q hq
        exact (hcop q (List.mem_cons_of_mem _ hq)).mul_left (hpairs.1 q hq)
      have hchildren : ∀ r : Fin (p ^ k), ∃ t : CoverTree,
          checkTree S M (d * p ^ k) (a + (d : ℤ) * r.val) t = true := by
        intro r
        exact ih (fun q hq => hpow q (List.mem_cons_of_mem _ hq)) hpairs.2 hcop' hM'
          hmod' (a + (d : ℤ) * r.val)
      choose children hc using hchildren
      refine ⟨.split p k children, ?_⟩
      simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      exact ⟨⟨hp, hk, hcop _ (List.mem_cons_self ..),
        (dvd_mul_right (d * p ^ k) rest.prod).trans hM'⟩, fun r _ => hc r⟩

/-- With a supplied prime power factorization of a common multiple,
a covering exists exactly when the tree checker accepts some certificate. -/
theorem covers_iff_exists_tree {S : Finset (ℕ × ℤ)} {factors : List ℕ}
    (hpow : ∀ q ∈ factors, ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ q = p ^ k)
    (hpair : factors.Pairwise Nat.Coprime) (hmod : ∀ s ∈ S, s.1 ∣ factors.prod) :
    Covers S ↔ ∃ t : CoverTree, checkTree S factors.prod 1 0 t = true := by
  constructor
  · intro hS
    exact exists_tree_of_factors hS factors hpow hpair
      (by intro q _; exact Nat.coprime_one_left q) (by simp) (by simpa using hmod) 0
  · rintro ⟨t, ht⟩
    exact covers_of_tree ht

end LeanLab.OpenProblems.Erdos273

#print axioms LeanLab.OpenProblems.Erdos273.exists_refined_class
#print axioms LeanLab.OpenProblems.Erdos273.checkTree_sound
#print axioms LeanLab.OpenProblems.Erdos273.covers_of_tree

#print axioms LeanLab.OpenProblems.Erdos273.check_selfridge_tree
#print axioms LeanLab.OpenProblems.Erdos273.covers_selfridge_tree
#print axioms LeanLab.OpenProblems.Erdos273.check_single_pair_false

#print axioms LeanLab.OpenProblems.Erdos273.checkCover_of_covers
#print axioms LeanLab.OpenProblems.Erdos273.checkCover_of_tree
#print axioms LeanLab.OpenProblems.Erdos273.checkTree_single_pair_false

#print axioms LeanLab.OpenProblems.Erdos273.exists_tree_of_factors
#print axioms LeanLab.OpenProblems.Erdos273.covers_iff_exists_tree

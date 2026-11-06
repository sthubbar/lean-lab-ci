import LeanLab.ChenDoubleSieve.Decomp392c

/-!
The explicit lower Rosser coefficient and its elementary support properties.
Source: https://doi.org/10.4064/aa-37-1-307-320, page 313 before Lemma 2.
This supplies no estimate of the weighted reciprocal main term.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset List
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task392

/-- The distinct prime factors in decreasing order. -/
def rosserFactors (d : ℕ) : List ℕ := d.primeFactors.sort (· ≥ ·)

/-- The lower Rosser coefficient from the displayed definition on page 313.
It is zero off squarefree integers and when an even length support test fails. -/
def rosserLowerWeight (D : ℝ) (d : ℕ) : ℝ :=
  if Squarefree d ∧ ∀ i : ℕ, ∀ hi : i < (rosserFactors d).length, Odd i →
      (((rosserFactors d).take i).prod : ℝ) * ((rosserFactors d)[i] : ℝ) ^ 3 < D
    then (-1 : ℝ) ^ (rosserFactors d).length else 0

/-- The coefficient has absolute value at most one. -/
theorem rosserLowerWeight_abs_le (D : ℝ) (d : ℕ) : |rosserLowerWeight D d| ≤ 1 := by
  unfold rosserLowerWeight
  split_ifs <;> simp [abs_pow]

/-- The empty prime factor list gives coefficient one at modulus one. -/
theorem rosserLowerWeight_one (D : ℝ) : rosserLowerWeight D 1 = 1 := by
  simp [rosserLowerWeight, rosserFactors]

/-- Nonsquarefree integers have zero coefficient. -/
theorem rosserLowerWeight_not_squarefree (D : ℝ) {d : ℕ} (hd : ¬Squarefree d) :
    rosserLowerWeight D d = 0 := by
  simp [rosserLowerWeight, hd]

/-- A squarefree modulus is the product of its decreasing factor list. -/
theorem rosserFactors_prod {d : ℕ} (hd : Squarefree d) : (rosserFactors d).prod = d := by
  change (↑(d.primeFactors.sort (· ≥ ·)) : Multiset ℕ).prod = d
  rw [Finset.sort_eq]
  rw [Finset.prod_val]
  exact Nat.prod_primeFactors_of_squarefree hd

/-- A nonzero lower coefficient splits into natural factors under the stated
prime square cutoff. This is the elementary support assertion of equation 14. -/
theorem rosserLowerWeight_factorization (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (d : ℕ) (hw : rosserLowerWeight (M * N) d ≠ 0)
    (hcut : ∀ p ∈ d.primeFactors, (p : ℝ) ^ 2 ≤ M * N) :
    ∃ d1 d2 : ℕ, d = d1 * d2 ∧ (d1 : ℝ) ≤ M ∧ (d2 : ℝ) ≤ N := by
  have hgood : Squarefree d ∧ ∀ i : ℕ, ∀ hi : i < (rosserFactors d).length, Odd i →
      (((rosserFactors d).take i).prod : ℝ) * ((rosserFactors d)[i] : ℝ) ^ 3 < M * N := by
    by_contra h
    exact hw (ite_eq_right h)
  let l := rosserFactors d
  have hmem : ∀ p ∈ l, p.Prime := by
    intro p hp
    exact (Nat.mem_primeFactors.mp (by simpa [l, rosserFactors] using hp)).1
  have hreal := rosser_prefix_bound (l.map (fun p : ℕ => (p : ℝ))) (M * N)
  have hone : ∀ x ∈ l.map (fun p : ℕ => (p : ℝ)), 1 ≤ x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact_mod_cast (hmem p hp).one_lt.le
  have hdesc : ∀ i : ℕ, ∀ hi : i + 1 < (l.map (fun p : ℕ => (p : ℝ))).length,
      (l.map (fun p : ℕ => (p : ℝ)))[i + 1] ≤ (l.map (fun p : ℕ => (p : ℝ)))[i] := by
    intro i hi
    have hi' : i + 1 < l.length := by simpa using hi
    have hsort : l.Pairwise (· ≥ ·) := Finset.pairwise_sort _ _
    have hp := List.pairwise_iff_getElem.mp hsort i (i + 1) (by omega) hi' (by omega)
    simpa using (show (l[i + 1] : ℝ) ≤ l[i] by exact_mod_cast hp)
  have hfirst : ∀ h : 0 < (l.map (fun p : ℕ => (p : ℝ))).length,
      (l.map (fun p : ℕ => (p : ℝ)))[0] ^ 2 ≤ M * N := by
    intro h
    have hl : 0 < l.length := by simpa using h
    have hp : l[0] ∈ d.primeFactors := by
      exact (Finset.mem_sort (· ≥ ·)).mp (List.getElem_mem hl)
    simpa using hcut l[0] hp
  have hs : ∀ i : ℕ, ∀ hi : i < (l.map (fun p : ℕ => (p : ℝ))).length, Odd i →
      ((l.map (fun p : ℕ => (p : ℝ))).take i).prod *
        (l.map (fun p : ℕ => (p : ℝ)))[i] ^ 3 ≤ M * N := by
    intro i hi hodd
    have hi' : i < l.length := by simpa using hi
    have hh := (hgood.2 i hi' hodd).le
    simpa only [← List.map_take, List.getElem_map, ← Nat.cast_list_prod] using hh
  have hp := hreal hone hdesc hfirst hs
  have hpnat : ∀ i : ℕ, ∀ hi : i < l.length,
      ((l.take i).prod : ℝ) * (l[i] : ℝ) ^ 2 ≤ M * N := by
    intro i hi
    have hh := hp i (by simpa using hi)
    rw [← List.map_take, ← Nat.cast_list_prod,
      List.getElem_map (fun p : ℕ => (p : ℝ))] at hh
    exact hh
  obtain ⟨a, b, hab, ha, hb⟩ := nat_factor_partition l M N hM hN hpnat
  refine ⟨a.prod, b.prod, ?_, ha, hb⟩
  calc
    d = l.prod := (rosserFactors_prod hgood.1).symm
    _ = (a ++ b).prod := hab.prod_eq
    _ = a.prod * b.prod := List.prod_append

/-- The same cutoff puts every nonzero coefficient at level D. -/
theorem rosserLowerWeight_level (D : ℝ) (hD : 1 ≤ D) (d : ℕ)
    (hw : rosserLowerWeight D d ≠ 0)
    (hcut : ∀ p ∈ d.primeFactors, (p : ℝ) ^ 2 ≤ D) : (d : ℝ) ≤ D := by
  have hw' : rosserLowerWeight (1 * D) d ≠ 0 := by simpa using hw
  obtain ⟨d1, d2, heq, hd1, hd2⟩ := rosserLowerWeight_factorization 1 D
    (by norm_num) hD d hw' (by simpa using hcut)
  have hd1le : d1 ≤ 1 := by exact_mod_cast hd1
  have hdpos : d ≠ 0 := by
    intro h
    rw [h] at hw
    simp [rosserLowerWeight] at hw
  have hd1ne : d1 ≠ 0 := by intro h; simp [h] at heq; exact hdpos heq
  have hd1eq : d1 = 1 := by omega
  rw [hd1eq, one_mul] at heq
  rw [heq]
  exact hd2

/-- A nontrivial squarefree modulus has a nonzero lower coefficient. -/
theorem rosserLowerWeight_instance : rosserLowerWeight 150 30 = -1 := by
  have hf : rosserFactors 30 = [5, 3, 2] := by
    unfold rosserFactors
    have hpf : (30 : ℕ).primeFactors = {2, 3, 5} := by decide +kernel
    have he : ({2, 3, 5} : Finset ℕ) = ([5, 3, 2] : List ℕ).toFinset := by decide
    rw [hpf, he]
    exact (List.toFinset_sort (r := (· ≥ ·)) (by decide : ([5, 3, 2] : List ℕ).Nodup)).2
      (by decide)
  have hs : Squarefree (30 : ℕ) := by decide +kernel
  have ht : ∀ i : ℕ, ∀ hi : i < (rosserFactors 30).length, Odd i →
      (((rosserFactors 30).take i).prod : ℝ) * ((rosserFactors 30)[i] : ℝ) ^ 3 < 150 := by
    intro i hi hodd
    have hi3 : i < 3 := by simpa [hf] using hi
    have hi1 : i = 1 := by rw [Nat.odd_iff] at hodd; omega
    subst i
    norm_num [hf]
  rw [rosserLowerWeight, ite_eq_left ⟨hs, ht⟩, hf]
  norm_num

/-- The actual nonzero coefficient has a natural factorization with both bounds. -/
theorem rosserLowerWeight_factorization_instance : ∃ d1 d2 : ℕ,
    30 = d1 * d2 ∧ (d1 : ℝ) ≤ 10 ∧ (d2 : ℝ) ≤ 15 := by
  apply rosserLowerWeight_factorization 10 15 (by norm_num) (by norm_num) 30
  · norm_num [rosserLowerWeight_instance]
  · intro p hp
    have hf : (30 : ℕ).primeFactors = {2, 3, 5} := by decide +kernel
    rw [hf] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num

end LeanLab.ChenDoubleSieve.Task392

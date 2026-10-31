/-
P0044, page 601 display 4.3. Normalization of the linear sieve constant.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Statements
import LeanLab.ChenExplicit.Reductions
open Finset
noncomputable section
namespace LeanLab.Cai2002

/-- The prime local factor for the sieve constant in page 601 display 4.3. -/
def sieveLocal118 (N p : ℕ) : ℝ :=
  if p ∣ N then (1 - 1 / (p : ℝ))⁻¹
  else (1 - 1 / ((p : ℝ) - 1)) * (1 - 1 / (p : ℝ))⁻¹

/-- The finite correction at an odd prime divisor of N in page 601 display 4.3. -/
def oddCorrection118 (N p : ℕ) : ℝ :=
  if p ∣ N then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1

/-- The local algebra in page 601 display 4.3, for every odd prime and also every p above two. -/
theorem sieveLocal118_eq (N p : ℕ) (hp : 2 < p) :
    sieveLocal118 N p = (1 - 1 / ((p : ℝ) - 1) ^ 2) * oddCorrection118 N p := by
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
  unfold sieveLocal118 oddCorrection118
  split_ifs <;> field_simp <;> ring


/-- The odd correction product is finite, page 601 display 4.3. -/
theorem oddCorrection118_product (N : ℕ) (hN : N ≠ 0) :
    (∏' p : {p : ℕ // p.Prime ∧ 2 < p}, oddCorrection118 N p) =
      ∏ p ∈ N.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  classical
  let T := N.primeFactors.subtype (fun p => p.Prime ∧ 2 < p)
  have hsupport : ∀ p : {p : ℕ // p.Prime ∧ 2 < p}, p ∉ T → oddCorrection118 N p = 1 := by
    intro p hp
    apply ite_eq_right
    intro hd
    exact hp (by simpa [T] using (show (p : ℕ) ∈ N.primeFactors from
      Nat.mem_primeFactors.mpr ⟨p.2.1, hd, hN⟩))
  rw [tprod_eq_prod hsupport]
  change (∏ p ∈ N.primeFactors.subtype (fun p => p.Prime ∧ 2 < p),
    oddCorrection118 N p) = _
  rw [prod_subtype_eq_prod_filter]
  have hfilter : N.primeFactors.filter (fun p => p.Prime ∧ 2 < p) =
      N.primeFactors.filter (2 < ·) := by
    ext p
    simp only [mem_filter]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, (Nat.prime_of_mem_primeFactors h.1), h.2⟩⟩
  rw [hfilter]
  apply prod_congr rfl
  intro p hp
  exact ite_eq_left (Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1)

/-- The finite correction product converges, page 601 display 4.3. -/
theorem oddCorrection118_multipliable (N : ℕ) (hN : N ≠ 0) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => oddCorrection118 N p) := by
  classical
  apply multipliable_of_ne_finset_one (s := N.primeFactors.subtype (fun p => p.Prime ∧ 2 < p))
  intro p hp
  apply ite_eq_right
  intro hd
  exact hp (by simpa using (show (p : ℕ) ∈ N.primeFactors from
    Nat.mem_primeFactors.mpr ⟨p.2.1, hd, hN⟩))

/-- The odd local product equals C, page 601 display 4.3. -/
theorem oddLocal118_product (N : ℕ) (hN : N ≠ 0) :
    (∏' p : {p : ℕ // p.Prime ∧ 2 < p}, sieveLocal118 N p) = C N := by
  calc
    (∏' p : {p : ℕ // p.Prime ∧ 2 < p}, sieveLocal118 N p) =
        ∏' p : {p : ℕ // p.Prime ∧ 2 < p},
          (1 - 1 / ((p : ℝ) - 1) ^ 2) * oddCorrection118 N p :=
      tprod_congr fun p => sieveLocal118_eq N p p.2.2
    _ = (∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p : ℝ) - 1) ^ 2)) *
        ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, oddCorrection118 N p :=
      LeanLab.ChenExplicit.twinC_multipliable.tprod_mul (oddCorrection118_multipliable N hN)
    _ = C N := by
      rw [oddCorrection118_product N hN]
      rfl

/-- Convergence of the odd local product, page 601 display 4.3. -/
theorem oddLocal118_multipliable (N : ℕ) (hN : N ≠ 0) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => sieveLocal118 N p) := by
  exact (LeanLab.ChenExplicit.twinC_multipliable.mul (oddCorrection118_multipliable N hN)).congr
    (fun p => (sieveLocal118_eq N p p.2.2).symm)

/-- Display 4.3 on page 601: the even prime factor times the odd product is twice C. -/
theorem sieve_constant118 (N : ℕ) (hN : N ≠ 0) (he : Even N) :
    sieveLocal118 N 2 *
      (∏' p : {p : ℕ // p.Prime ∧ 2 < p}, sieveLocal118 N p) = 2 * C N := by
  have h2 : 2 ∣ N := even_iff_two_dvd.mp he
  rw [oddLocal118_product N hN, sieveLocal118, ite_eq_left h2]
  norm_num

end LeanLab.Cai2002

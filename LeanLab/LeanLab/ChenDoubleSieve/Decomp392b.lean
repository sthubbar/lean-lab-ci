import LeanLab.ChenDoubleSieve.Decomp363d
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
Finite maximum comparison for the page 38 mean value specialization.
Source: https://arxiv.org/pdf/0705.1652, page 6 Lemma 2.3 and page 38.
Only natural endpoints are needed to dominate the actual fixed endpoint.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task392
open Task275 Task348 Task363

/-- The signed prime progression discrepancy at a natural endpoint. -/
def progressionError (y q a : ℕ) : ℝ :=
  (#((range (y + 1)).filter (fun p => p.Prime ∧ p % q = a % q)) : ℝ) -
    Wu04.li y / (q.totient : ℝ)

/-- Zero and the absolute errors at reduced residues and natural endpoints up to N. -/
def progressionErrors (N q : ℕ) : Finset ℝ :=
  insert 0 ((((Finset.Icc 2 N).product (range q)).filter
    (fun ya => ya.2.Coprime q)).image (fun ya => |progressionError ya.1 q ya.2|))

/-- A finite maximum dominated by the real endpoint maximum on page 38. -/
def progressionMax (N q : ℕ) : ℝ :=
  (progressionErrors N q).sup' (by exact ⟨0, mem_insert_self _ _⟩) id

/-- The finite maximum is nonnegative, including at modulus zero. -/
theorem progressionMax_nonneg (N q : ℕ) : 0 ≤ progressionMax N q := by
  exact Finset.le_sup' id (mem_insert_self _ _)

/-- Each reduced residue and natural endpoint occurs in the finite maximum. -/
theorem progressionError_le_max {N y q a : ℕ} (hy2 : 2 ≤ y) (hy : y ≤ N) (ha : a < q)
    (hcop : a.Coprime q) : |progressionError y q a| ≤ progressionMax N q := by
  apply Finset.le_sup' id
  apply Finset.mem_insert_of_mem
  apply mem_image.mpr
  exact ⟨(y, a), mem_filter.mpr
    ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hy2, hy⟩, mem_range.mpr ha⟩, hcop⟩, rfl⟩

/-- Residue reduction preserves the progression error exactly. -/
theorem progressionError_mod (y q a : ℕ) :
    progressionError y q (a % q) = progressionError y q a := by
  simp [progressionError]

/-- The exact prime difference discrepancy is bounded by the finite maximum. -/
theorem divisor_error_le_max {N q : ℕ} (hN : 2 ≤ N) (hq : 0 < q) (hcop : q.Coprime N) :
    |(#((primeSequence N).filter (fun a => q ∣ a)) : ℝ) -
      Wu04.li N / (q.totient : ℝ)| ≤ progressionMax N q := by
  rw [primeSequence_divisor_card]
  change |progressionError N q N| ≤ progressionMax N q
  rw [← progressionError_mod N q N]
  apply progressionError_le_max hN le_rfl (Nat.mod_lt _ hq)
  exact (ZMod.coprime_mod_iff_coprime N q).mpr hcop.symm

/-- The nonnegative squarefree weighted maximum in the page 38 display. -/
def meanValueSum (B : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ⌊sieveLevel B N⌋₊,
    (ArithmeticFunction.moebius q : ℝ) ^ 2 * progressionMax N q

/-- The fixed endpoint remainder is at most the squarefree weighted maximum.
No prime distribution estimate is used. -/
theorem rawRemainder_le_meanValueSum (B : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    rawRemainder B N ≤ meanValueSum B N := by
  calc
    _ ≤ ∑ q ∈ remainderModuli B N, progressionMax N q := by
      apply sum_le_sum
      intro q hq
      have hmem := mem_filter.mp hq
      exact divisor_error_le_max hN (by have := (mem_Icc.mp hmem.1).1; omega) hmem.2.2
    _ = ∑ q ∈ remainderModuli B N,
        (ArithmeticFunction.moebius q : ℝ) ^ 2 * progressionMax N q := by
      apply sum_congr rfl
      intro q hq
      have hsq := (mem_filter.mp hq).2.1
      have hmu : (ArithmeticFunction.moebius q : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
      rw [hmu, one_mul]
    _ ≤ meanValueSum B N := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro q hq
        exact (mem_filter.mp hq).1
      · intro q _ _
        exact mul_nonneg (sq_nonneg _) (progressionMax_nonneg N q)

/-- The cubic mean value input implies exactly the sealed remainder target.
The analytic estimate for meanValueSum remains an explicit premise. -/
theorem remainder_of_meanValue
    (hmean : ∃ B : ℝ, 0 < B ∧ ∃ D : ℝ, 0 ≤ D ∧
      ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
        meanValueSum B N ≤ D * (N : ℝ) / log N ^ 3) :
    ∃ B : ℝ, 0 < B ∧ ∃ D : ℝ, 0 ≤ D ∧
      ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
        rawRemainder B N ≤ D * (N : ℝ) / log N ^ 3 := by
  obtain ⟨B, hB, D, hD, M, hM⟩ := hmean
  refine ⟨B, hB, D, hD, max 2 M, ?_⟩
  intro N hEven hN
  exact (rawRemainder_le_meanValueSum B (by omega : 2 ≤ N)).trans
    (hM N hEven (by omega))

/-- The finite progression maximum increases with its endpoint range. -/
theorem progressionMax_mono {M N : ℕ} (hMN : M ≤ N) (q : ℕ) :
    progressionMax M q ≤ progressionMax N q := by
  apply Finset.sup'_le
  intro x hx
  apply Finset.le_sup' id
  rcases mem_insert.mp hx with rfl | hx
  · exact mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    obtain ⟨⟨y, a⟩, hya, rfl⟩ := mem_image.mp hx
    obtain ⟨hya, hcop⟩ := mem_filter.mp hya
    obtain ⟨hy, ha⟩ := mem_product.mp hya
    obtain ⟨hy2, hyM⟩ := mem_Icc.mp hy
    exact mem_image.mpr ⟨(y, a), mem_filter.mpr
      ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hy2, hyM.trans hMN⟩, ha⟩, hcop⟩, rfl⟩

/-- Every term in the squarefree weighted mean value sum is nonnegative. -/
theorem meanValueSum_nonneg (B : ℝ) (N : ℕ) : 0 ≤ meanValueSum B N := by
  exact sum_nonneg (fun q _ => mul_nonneg (sq_nonneg _) (progressionMax_nonneg N q))

/-- A concrete reduced residue at endpoint two gives a nonzero maximum. -/
theorem progressionMax_instance : 1 ≤ progressionMax 16 1 := by
  have h := progressionError_le_max (N := 16) (y := 2) (q := 1) (a := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [progressionError, Wu04.li, Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton] at h
  exact h

/-- Modulus one gives a nonzero term in the actual finite mean value domain. -/
theorem meanValueSum_instance : 1 ≤ meanValueSum 1 16 := by
  have hmem := (mem_filter.mp remainderModuli_instance).1
  have hs : (ArithmeticFunction.moebius 1 : ℝ) ^ 2 * progressionMax 16 1 ≤
      meanValueSum 1 16 := by
    unfold meanValueSum
    exact Finset.single_le_sum (s := Finset.Icc 1 ⌊sieveLevel 1 16⌋₊)
      (f := fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 * progressionMax 16 q)
      (a := 1) (fun q _ => mul_nonneg (sq_nonneg _) (progressionMax_nonneg 16 q)) hmem
  simpa using progressionMax_instance.trans (by simpa using hs)

end LeanLab.ChenDoubleSieve.Task392

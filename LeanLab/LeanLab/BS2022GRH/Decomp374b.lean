/- AI wrote this Lean code for CODEX task374. Goldbach is open.
The single endpoint, boundary correction and scalar comparison on journal p. 1224.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Decomp148a
import LeanLab.BS2022GRH.Prefix374

namespace LeanLab.BS2022GRH.Decomp374b
open Real Finset Classical ChenThresholdGRH Decomp148a
noncomputable section

/-- The character sum over primes up to a real endpoint, journal p. 1224. -/
def primePrefix (x : ℝ) {r : ℕ} (χ : DirichletCharacter ℂ r) : ℂ :=
  ∑ p ∈ (range (⌊x⌋₊ + 1)).filter (fun p => p.Prime), χ p

/-- LEAF. Journal p. 1224, the endpoint application of Lemma 3 before display 13.
Use Ernvall Hytonen and Palojarvi Theorem 1, arXiv 2003.01925 p. 2,
and cancellation of a nonprincipal character over the reduced residues.
This estimates one endpoint, not a prime interval.
CONDITIONAL ON the existing progression_at_endpoint input. The finite residue reduction is proved. -/
theorem prefix_bound (hG : GRH) (x : ℝ) (r : ℕ)
    (hx : 25 ≤ x) (hr : 3 ≤ r) (hrx : (r : ℝ) ≤ √x)
    (χ : DirichletCharacter ℂ r) (hχ : χ ≠ 1) :
    ‖primePrefix x χ‖ ≤ r.totient * (qG x * √x * log x) := by
  apply Prefix374.norm_sum_of_residue_errors _ r (by omega) χ hχ
  intro a ha
  have har : a % r = a := Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp ha).1)
  have hp := DecompC164a.progression_at_endpoint hG r a x hr hrx (mem_filter.mp ha).2
  simpa only [filter_filter, har] using hp

/-- Floor is at most ceiling. -/
private lemma floor_le_ceil' (x : ℝ) : ⌊x⌋₊ ≤ ⌈x⌉₊ := by
  by_cases h : 0 ≤ x
  · exact Nat.cast_le.mp (le_trans (Nat.floor_le h) (Nat.le_ceil x))
  · have h' : x < 0 := not_le.mp h
    rw [Nat.floor_eq_zero.mpr (by linarith : x < 1), Nat.ceil_eq_zero.mpr h'.le]

/-- The endpoint boundary correction is at most two character values.
The two prime sets differ only at the two integer endpoints of the range. -/
private theorem interval_boundary_aux (Y Z : ℝ) (r : ℕ)
    (hZ : 25 ≤ Z) (hZY : Z < Y) (χ : DirichletCharacter ℂ r) :
    ‖(∑ p ∈ pRange Y Z, χ p) - (primePrefix Y χ - primePrefix Z χ)‖ ≤ 2 := by
  classical
  have hZ0 : (0 : ℝ) ≤ Z := by linarith
  have hZYle : Z ≤ Y := hZY.le
  have hfl : ⌊Z⌋₊ ≤ ⌊Y⌋₊ := Nat.floor_mono hZYle
  have hceil : ⌈Y⌉₊ ≤ ⌊Y⌋₊ + 1 := by
    rw [Nat.ceil_le]
    push_cast
    exact (Nat.lt_floor_add_one Y).le
  have hfloorCeil : ⌊Y⌋₊ ≤ ⌈Y⌉₊ := floor_le_ceil' Y
  set S1 : Finset ℕ := (range (⌊Y⌋₊ + 1)).filter (fun p => p.Prime) with hS1
  set S2 : Finset ℕ := (range (⌊Z⌋₊ + 1)).filter (fun p => p.Prime) with hS2
  set S3 : Finset ℕ := pRange Y Z with hS3
  have m1 : ∀ p : ℕ, p ∈ S1 ↔ p.Prime ∧ p ≤ ⌊Y⌋₊ := by
    intro p
    simp only [hS1, mem_filter, mem_range, Nat.lt_succ_iff, and_comm]
  have m2 : ∀ p : ℕ, p ∈ S2 ↔ p.Prime ∧ p ≤ ⌊Z⌋₊ := by
    intro p
    simp only [hS2, mem_filter, mem_range, Nat.lt_succ_iff, and_comm]
  have m3 : ∀ p : ℕ, p ∈ S3 ↔ p.Prime ∧ Z ≤ (p : ℝ) ∧ p < ⌈Y⌉₊ := by
    intro p
    simp only [hS3, pRange, mem_filter, mem_range]
    tauto
  have hS2S1 : S2 ⊆ S1 := by
    intro p hp
    rw [m2] at hp
    exact (m1 p).mpr ⟨hp.1, le_trans hp.2 hfl⟩
  have hS3S1 : S3 ⊆ S1 := by
    intro p hp
    have hp3 := (m3 p).mp hp
    refine (m1 p).mpr ⟨hp3.1, ?_⟩
    omega
  -- elements of S3 that are also in S2 sit at the floor of Z
  have hS3S2 : S3 ∩ S2 ⊆ ({⌊Z⌋₊} : Finset ℕ) := by
    intro p hp
    rw [mem_inter] at hp
    obtain ⟨hp3, hp2⟩ := hp
    have h1 := (m3 p).mp hp3
    have h2 := (m2 p).mp hp2
    simp only [mem_singleton]
    have heq : ((p : ℕ) : ℝ) = ((⌊Z⌋₊ : ℕ) : ℝ) :=
      le_antisymm (by exact_mod_cast h2.2) (le_trans (Nat.floor_le hZ0) h1.2.1)
    exact Nat.cast_injective heq
  have hEsing : S3 \ (S1 \ S2) ⊆ ({⌊Z⌋₊} : Finset ℕ) := by
    intro p hp
    rw [mem_sdiff] at hp
    obtain ⟨hp3, hpd⟩ := hp
    have hp2 : p ∈ S2 := by
      by_contra hcon
      exact hpd (by rw [mem_sdiff]; exact ⟨hS3S1 hp3, hcon⟩)
    exact hS3S2 (by rw [mem_inter]; exact ⟨hp3, hp2⟩)
  have hFsing : (S1 \ S2) \ S3 ⊆ ({⌊Y⌋₊} : Finset ℕ) := by
    intro p hp
    rw [mem_sdiff, mem_sdiff] at hp
    obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
    have h1 := (m1 p).mp hp1
    have hpgt : ⌊Z⌋₊ < p := by
      by_contra hle
      exact hp2 ((m2 p).mpr ⟨h1.1, not_lt.mp hle⟩)
    have hpZ : Z ≤ (p : ℝ) := by
      have hcast : (⌊Z⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by
        have h2 : ⌊Z⌋₊ + 1 ≤ p := hpgt
        exact_mod_cast h2
      linarith [Nat.lt_floor_add_one Z]
    have hge : ⌈Y⌉₊ ≤ p := by
      by_contra hlt
      exact hp3 ((m3 p).mpr ⟨h1.1, hpZ, not_le.mp hlt⟩)
    simp only [mem_singleton]
    exact le_antisymm h1.2 (le_trans hfloorCeil hge)
  have hcardE : (S3 \ (S1 \ S2)).card ≤ 1 :=
    Finset.card_le_one.mpr (fun a ha b hb => by
      have ha' : a = ⌊Z⌋₊ := by simpa using hEsing ha
      have hb' : b = ⌊Z⌋₊ := by simpa using hEsing hb
      rw [ha', hb'])
  have hcardF : ((S1 \ S2) \ S3).card ≤ 1 :=
    Finset.card_le_one.mpr (fun a ha b hb => by
      have ha' : a = ⌊Y⌋₊ := by simpa using hFsing ha
      have hb' : b = ⌊Y⌋₊ := by simpa using hFsing hb
      rw [ha', hb'])
  have hnormE : ‖∑ p ∈ S3 \ (S1 \ S2), χ p‖ ≤ 1 := by
    have h1 : ‖∑ p ∈ S3 \ (S1 \ S2), χ p‖ ≤ ((S3 \ (S1 \ S2)).card : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ p ∈ S3 \ (S1 \ S2), ‖χ p‖ ≤ ∑ _p ∈ S3 \ (S1 \ S2), (1 : ℝ) :=
            Finset.sum_le_sum (fun p _ => χ.norm_le_one p)
        _ = ((S3 \ (S1 \ S2)).card : ℝ) := by simp
    have h2 : ((S3 \ (S1 \ S2)).card : ℝ) ≤ 1 := by
      have h3 : ((S3 \ (S1 \ S2)).card : ℝ) ≤ ((1 : ℕ) : ℝ) := by exact_mod_cast hcardE
      simpa using h3
    linarith
  have hnormF : ‖∑ p ∈ (S1 \ S2) \ S3, χ p‖ ≤ 1 := by
    have h1 : ‖∑ p ∈ (S1 \ S2) \ S3, χ p‖ ≤ (((S1 \ S2) \ S3).card : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ p ∈ (S1 \ S2) \ S3, ‖χ p‖ ≤ ∑ _p ∈ (S1 \ S2) \ S3, (1 : ℝ) :=
            Finset.sum_le_sum (fun p _ => χ.norm_le_one p)
        _ = (((S1 \ S2) \ S3).card : ℝ) := by simp
    have h2 : (((S1 \ S2) \ S3).card : ℝ) ≤ 1 := by
      have h3 : (((S1 \ S2) \ S3).card : ℝ) ≤ ((1 : ℕ) : ℝ) := by exact_mod_cast hcardF
      simpa using h3
    linarith
  have hD : (∑ p ∈ S1, χ p) - (∑ p ∈ S2, χ p) = ∑ p ∈ S1 \ S2, χ p := by
    have h := Finset.sum_sdiff (s₁ := S2) (s₂ := S1) (f := fun p => χ p) hS2S1
    rw [← h]
    ring
  have hsplit3 : (∑ p ∈ S3, χ p) =
      ∑ p ∈ S3 ∩ (S1 \ S2), χ p + ∑ p ∈ S3 \ (S1 \ S2), χ p := by
    have h := Finset.sum_sdiff (s₁ := S3 ∩ (S1 \ S2)) (s₂ := S3)
      (f := fun p => χ p) inter_subset_left
    rw [← h]
    have hEq : S3 \ (S3 ∩ (S1 \ S2)) = S3 \ (S1 \ S2) := by
      ext p
      simp only [mem_sdiff, mem_inter]
      tauto
    rw [hEq]
    ring
  have hsplitD : (∑ p ∈ S1 \ S2, χ p) =
      ∑ p ∈ S3 ∩ (S1 \ S2), χ p + ∑ p ∈ (S1 \ S2) \ S3, χ p := by
    have h := Finset.sum_sdiff (s₁ := S3 ∩ (S1 \ S2)) (s₂ := S1 \ S2)
      (f := fun p => χ p) inter_subset_right
    rw [← h]
    have hEq : (S1 \ S2) \ (S3 ∩ (S1 \ S2)) = (S1 \ S2) \ S3 := by
      ext p
      simp only [mem_sdiff, mem_inter]
      tauto
    rw [hEq]
    ring
  rw [primePrefix, primePrefix, ← hS1, ← hS2, hD, hsplit3, hsplitD]
  have hzero : (∑ p ∈ S3 ∩ (S1 \ S2), χ p + ∑ p ∈ S3 \ (S1 \ S2), χ p) -
      (∑ p ∈ S3 ∩ (S1 \ S2), χ p + ∑ p ∈ (S1 \ S2) \ S3, χ p) =
      ∑ p ∈ S3 \ (S1 \ S2), χ p - ∑ p ∈ (S1 \ S2) \ S3, χ p := by
    ring
  rw [hzero]
  exact (norm_sub_le _ _).trans (by linarith)

/-- LEAF. Journal p. 1224, the endpoint correction E before display 13.
Each of the two possible prime endpoints contributes at most one.
This finite correction has no GRH or progression estimate. -/
theorem interval_boundary (Y Z : ℝ) (r : ℕ)
    (hZ : 25 ≤ Z) (hZY : Z < Y) (χ : DirichletCharacter ℂ r) :
    ‖(∑ p ∈ pRange Y Z, χ p) - (primePrefix Y χ - primePrefix Z χ)‖ ≤ 2 :=
  interval_boundary_aux Y Z r hZ hZY χ

/-- LEAF. Journal p. 1224, the last scalar comparison before display 13.
The whole error envelope increases on this ray. Antitonicity of qG alone is insufficient. -/
theorem error_envelope_mono (Y Z : ℝ) (hZ : 25 ≤ Z) (hZY : Z < Y) :
    qG Z * √Z * log Z ≤ qG Y * √Y * log Y := by
  sorry

/-- Exact statement of Decomp148b.prime_character_bound from the three smaller steps.
CONDITIONAL ON prefix_bound, interval_boundary and error_envelope_mono. -/
theorem prime_character_bound (hG : GRH) (Y Z : ℝ) (r : ℕ)
    (hZ : 25 ≤ Z) (hZY : Z < Y) (hr : 3 ≤ r) (hrZ : (r : ℝ) ≤ √Z)
    (χ : DirichletCharacter ℂ r) (hχ : χ ≠ 1) :
    ‖∑ p ∈ pRange Y Z, χ p‖ ≤ 2 * r.totient * (1 + qG Y * √Y * log Y) := by
  have hy : 25 ≤ Y := hZ.trans hZY.le
  have hY := prefix_bound hG Y r hy hr (hrZ.trans (sqrt_le_sqrt hZY.le)) χ hχ
  have hZ' := prefix_bound hG Z r hZ hr hrZ χ hχ
  have hm := error_envelope_mono Y Z hZ hZY
  have he := interval_boundary Y Z r hZ hZY χ
  have ht := norm_sub_le (primePrefix Y χ) (primePrefix Z χ)
  have hi := norm_add_le
    ((∑ p ∈ pRange Y Z, χ p) - (primePrefix Y χ - primePrefix Z χ))
    (primePrefix Y χ - primePrefix Z χ)
  rw [sub_add_cancel] at hi
  have hφ : (1 : ℝ) ≤ r.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < r)
  have hm' := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ r.totient)
  calc
    _ ≤ 2 + r.totient * (qG Y * √Y * log Y) +
        r.totient * (qG Z * √Z * log Z) := by linarith
    _ ≤ 2 * r.totient * (1 + qG Y * √Y * log Y) := by nlinarith

end
end LeanLab.BS2022GRH.Decomp374b

#print axioms LeanLab.BS2022GRH.Decomp374b.prefix_bound
#print axioms LeanLab.BS2022GRH.Decomp374b.interval_boundary
#print axioms LeanLab.BS2022GRH.Decomp374b.error_envelope_mono
#print axioms LeanLab.BS2022GRH.Decomp374b.prime_character_bound

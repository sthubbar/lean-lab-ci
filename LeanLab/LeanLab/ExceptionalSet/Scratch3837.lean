import Mathlib.Analysis.PSeries

open Finset

namespace Scratch3837

theorem sum_inv_sq_pos_le (K : ℕ) (hK : 1 ≤ K) (S : Finset ℤ)
    (hSpos : ∀ h ∈ S, 0 < h) (hSabs : ∀ h ∈ S, K < |h|) :
    (∑ h ∈ S, 1 / (h : ℝ) ^ 2) ≤ (K : ℝ)⁻¹ := by
  classical
  by_cases hne : S.Nonempty
  · let T : Finset ℕ := S.image Int.natAbs
    have hTne : T.Nonempty := Finset.image_nonempty.mpr hne
    let M : ℕ := T.max' hTne
    have hM : ∀ n ∈ T, n ≤ M := by
      intro n hn
      exact Finset.le_max' T n hTne
    obtain ⟨h0, h0S⟩ := hne
    have hKle : K ≤ M := by
      have h0T : h0.natAbs ∈ T := by simp [T, h0S]
      have h0abs : K < h0.natAbs := by
        have := hSabs h0 h0S
        rw [Int.natCast_natAbs] at this
        exact_mod_cast this
      have h0le : h0.natAbs ≤ M := hM _ h0T
      exact_mod_cast (Nat.le_of_lt h0abs).trans h0le
    have hsub : T ⊆ Finset.Ioc K M := by
      intro n hn
      refine Finset.mem_Ioc.mpr ⟨?_, hM n hn⟩
      obtain ⟨h, hS, rfl⟩ := Finset.mem_image.mp hn
      have := hSabs h hS
      rw [Int.natCast_natAbs] at this
      exact_mod_cast this
    calc
      (∑ h ∈ S, 1 / (h : ℝ) ^ 2) = ∑ n ∈ T, (n : ℝ)⁻² := by
        refine Finset.sum_bij (s := S) (t := T)
          (f := fun h : ℤ => 1 / (h : ℝ) ^ 2)
          (g := fun n : ℕ => (n : ℝ)⁻²) (fun h _ => h.natAbs) ?_ ?_ ?_ ?_
        · intro h hh
          simp [T]
        · intro h1 h1S h2 h2S heq
          have heq' : (h1.natAbs : ℤ) = (h2.natAbs : ℤ) := by exact_mod_cast heq
          have h1eq : h1 = (h1.natAbs : ℤ) := Int.natAbs_of_nonneg (le_of_lt (hSpos h1 h1S))
          have h2eq : h2 = (h2.natAbs : ℤ) := Int.natAbs_of_nonneg (le_of_lt (hSpos h2 h2S))
          rw [h1eq, h2eq] at heq'
          exact heq'
        · intro n hn
          obtain ⟨h, hS, rfl⟩ := Finset.mem_image.mp hn
          exact ⟨h, hS, rfl⟩
        · intro h hh
          simp only [div_eq_mul_inv]
          rw [← Int.natAbs_sq h]
      _ ≤ ∑ n ∈ Finset.Ioc K M, (n : ℝ)⁻² := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro n hn hn'
        positivity
      _ ≤ (K : ℝ)⁻¹ := by
        calc
          (∑ n ∈ Finset.Ioc K M, (n : ℝ)⁻²) ≤ (K : ℝ)⁻¹ - (M : ℝ)⁻¹ := by
            simpa using (sum_Ioc_inv_sq_le_sub (α := ℝ) (by omega) (by omega))
          _ ≤ (K : ℝ)⁻¹ := by linarith [inv_nonneg (M : ℝ)]
  · have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [this]

theorem sum_inv_sq_int_le (K : ℕ) (hK : 1 ≤ K) (S : Finset ℤ)
    (hSabs : ∀ h ∈ S, K < |h|) :
    (∑ h ∈ S, 1 / (h : ℝ) ^ 2) ≤ 2 / (K : ℝ) := by
  classical
  let Sp : Finset ℤ := S.filter (fun h => 0 < h)
  let Sn : Finset ℤ := S.filter (fun h => h < 0)
  let Tn : Finset ℤ := Sn.image Int.neg
  have hSnpos : ∀ h ∈ Tn, 0 < h := by
    intro h hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    have : x < 0 := by simpa [Sn] using hx
    positivity
  have hTnabs : ∀ h ∈ Tn, K < |h| := by
    intro h hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    have hxSn : x ∈ Sn := by simpa [Sn] using hx
    have hsabs := hSabs x hxSn
    rw [abs_neg] at hsabs
    simpa using hsabs
  have hpos := sum_inv_sq_pos_le K hK Sp (by
    intro h hh
    simpa [Sp] using hh) (by
    intro h hh
    have hh' : h ∈ S := by simpa [Sp] using hh
    simpa using hSabs h hh')
  have hneg : (∑ h ∈ Tn, 1 / (h : ℝ) ^ 2) ≤ (K : ℝ)⁻¹ :=
    sum_inv_sq_pos_le K hK Tn hSnpos hTnabs
  have hneg_eq : (∑ h ∈ Sn, 1 / (h : ℝ) ^ 2) =
      ∑ h ∈ Tn, 1 / (h : ℝ) ^ 2 := by
    refine Finset.sum_bij (s := Sn) (t := Tn)
      (f := fun h : ℤ => 1 / (h : ℝ) ^ 2)
      (g := fun h : ℤ => 1 / (h : ℝ) ^ 2) (fun h _ => -h) ?_ ?_ ?_ ?_
    · intro h hh
      simp [Tn]
    · intro h1 h1S h2 h2S heq
      apply Int.neg_injective
      simpa using heq
    · intro h hn
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
      exact ⟨x, hx, rfl⟩
    · intro h hh
      simp
  have hsplit : (∑ h ∈ S, 1 / (h : ℝ) ^ 2) =
      (∑ h ∈ Sp, 1 / (h : ℝ) ^ 2) + (∑ h ∈ Sn, 1 / (h : ℝ) ^ 2) := by
    rw [← Finset.sum_union Sp Sn]
    apply Finset.sum_congr rfl
    intro h hh
    by_cases hp : 0 < h
    · simp [Sp, Sn, hp]
    · by_cases hn : h < 0
      · simp [Sp, Sn, hp, hn]
      · have : h = 0 := by omega
        subst h
        have := hSabs 0 (by simpa [Sp, Sn, hp, hn] using hh)
        omega
  rw [hsplit, hneg_eq]
  linarith

end Scratch3837

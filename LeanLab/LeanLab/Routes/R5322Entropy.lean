/-
R-5322, CLOUD 20261021T0117Z-cloud55, unit U-6809, T3 MOONSHOT.
AI wrote this Lean code. Not progress on binary Goldbach, which is OPEN.

The Shannon entropy route.  Let w ≥ 0 be weights on a finite set s of even
numbers, for example w N = r(N), the Goldbach count, and T = Σ w.  Put
  entW s w = Σ_{n ∈ s} w n · log (T / w n) = T · H(μ),  μ = w / T,
with the convention 0 · log (T/0) = 0, which Lean's log 0 = 0 gives for free.
Plain math twins:
* `entW_le_log_support`: T·H(μ) ≤ T·log |supp w|, the Shannon form of the
  sumset size bound |supp| ≥ exp H, the bound Ruzsa and Tao use to turn
  sumset cardinality into entropy.
* `coverage_of_entropy`: if T·H(μ) > T·log(|s| - 1) then w n > 0 at EVERY
  n ∈ s.  This is the only way entropy alone can certify that every even N in a
  window is a sum of two primes, and it needs the entropy deficit
  log|s| - H(μ) below log(|s|/(|s| - 1)) ≈ 1/|s|.
* `uniform_ent`, `uniform_three_covers`: the hypothesis of
  `coverage_of_entropy` is satisfiable, by the uniform weight, so the lemma is
  not vacuous.
The numerics r5322_entropy_U6809.py show the Goldbach deficit is about 0.083,
the entropy of the singular series fluctuation, for X up to 4·10^6, so the
hypothesis of `coverage_of_entropy` fails for r by a factor 8·10^4 at X = 4·10^6.
-/
import Mathlib

namespace LeanLab.Routes.R5322

open Finset

/-- Unnormalized Shannon entropy T·H(w/T) of a nonnegative weight on s. -/
noncomputable def entW (s : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ s, w n * Real.log ((∑ m ∈ s, w m) / w n)

theorem entW_le_log_support (s : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ n ∈ s, 0 ≤ w n)
    (hT : 0 < ∑ m ∈ s, w m) :
    entW s w ≤ (∑ m ∈ s, w m) * Real.log ((s.filter (fun n => 0 < w n)).card) := by
  set T := ∑ m ∈ s, w m with hTdef
  set S := s.filter (fun n => 0 < w n) with hS
  have hsumS : ∑ n ∈ S, w n = T := by
    rw [hTdef, hS, Finset.sum_filter_of_ne]
    intro n hn hne
    exact lt_of_le_of_ne (hw n hn) (Ne.symm hne)
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsumS
    linarith
  have hk : (0:ℝ) < S.card := by exact_mod_cast hSne.card_pos
  have hent : entW s w = ∑ n ∈ S, w n * Real.log (T / w n) := by
    unfold entW
    rw [hS, Finset.sum_filter_of_ne]
    intro n hn hne
    rcases (hw n hn).lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [← h]; simp) hne
  rw [hent]
  have key : ∀ n ∈ S,
      w n * Real.log (T / w n) - w n * Real.log S.card ≤ T / S.card - w n := by
    intro n hn
    have hwn : 0 < w n := (Finset.mem_filter.mp hn).2
    have hx : 0 < T / (w n * S.card) := by positivity
    have hl := Real.log_le_sub_one_of_pos hx
    have e : Real.log (T / w n) - Real.log S.card = Real.log (T / (w n * S.card)) := by
      rw [← Real.log_div (by positivity) hk.ne']
      congr 1
      field_simp
    calc w n * Real.log (T / w n) - w n * Real.log S.card
        = w n * Real.log (T / (w n * S.card)) := by rw [← e]; ring
      _ ≤ w n * (T / (w n * S.card) - 1) := mul_le_mul_of_nonneg_left hl hwn.le
      _ = T / S.card - w n := by field_simp
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.sum_mul, hsumS] at hsum
  have hc : (S.card : ℝ) * (T / S.card) = T := by field_simp
  linarith

theorem coverage_of_entropy (s : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ n ∈ s, 0 ≤ w n)
    (hT : 0 < ∑ m ∈ s, w m)
    (hH : (∑ m ∈ s, w m) * Real.log ((s.card : ℝ) - 1) < entW s w) :
    ∀ n ∈ s, 0 < w n := by
  intro n hn
  by_contra hneg
  have hzero : ¬ (0 < w n) := hneg
  have hb := entW_le_log_support s w hw hT
  set S := s.filter (fun n => 0 < w n) with hS
  have hsub : S ⊆ s.erase n := by
    intro m hm
    rw [Finset.mem_filter] at hm
    refine Finset.mem_erase.mpr ⟨?_, hm.1⟩
    rintro rfl
    exact hzero hm.2
  have hcardN : S.card ≤ s.card - 1 := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_erase_of_mem hn] at this
  have h1 : 1 ≤ s.card := Finset.card_pos.mpr ⟨n, hn⟩
  have hSpos : 0 < S.card := by
    rcases Nat.eq_zero_or_pos S.card with h | h
    · exfalso
      rw [Finset.card_eq_zero] at h
      have : ∑ m ∈ s, w m = ∑ m ∈ S, w m := by
        rw [hS, Finset.sum_filter_of_ne]
        intro m hm hne
        exact lt_of_le_of_ne (hw m hm) (Ne.symm hne)
      rw [this, h, Finset.sum_empty] at hT
      exact lt_irrefl 0 hT
    · exact h
  have hcardR : (S.card : ℝ) ≤ (s.card : ℝ) - 1 := by
    have : ((s.card - 1 : ℕ) : ℝ) = (s.card : ℝ) - 1 := by
      rw [Nat.cast_sub h1, Nat.cast_one]
    rw [← this]; exact_mod_cast hcardN
  have hlog : Real.log S.card ≤ Real.log ((s.card : ℝ) - 1) :=
    Real.log_le_log (by exact_mod_cast hSpos) hcardR
  have := mul_le_mul_of_nonneg_left hlog hT.le
  linarith

/-- Vacuity test: the uniform weight on k points has T·H = k·log k. -/
theorem uniform_ent (k : ℕ) :
    entW (Finset.range k) (fun _ => 1) = k * Real.log k := by
  unfold entW
  simp

/-- The coverage hypothesis is satisfiable: uniform weight on {0, 1, 2}. -/
theorem uniform_three_covers :
    ∀ n ∈ Finset.range 3, (0:ℝ) < (fun _ => (1:ℝ)) n := by
  apply coverage_of_entropy
  · intro n _; norm_num
  · simp
  · rw [uniform_ent 3]
    simp
    norm_num
    exact Real.log_lt_log (by norm_num) (by norm_num)

end LeanLab.Routes.R5322

#print axioms LeanLab.Routes.R5322.entW_le_log_support
#print axioms LeanLab.Routes.R5322.coverage_of_entropy
#print axioms LeanLab.Routes.R5322.uniform_ent
#print axioms LeanLab.Routes.R5322.uniform_three_covers

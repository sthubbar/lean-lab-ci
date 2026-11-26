/-
Rational frequency separation in P0013 page 45, proof of Lemma 4.3.
These are geometric inputs. The prime supported operator estimate remains open.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Decomp119

namespace LeanLab.HelfgottArcs.Cluster707
open Finset
open LeanLab.HelfgottArcs.Decomp119

/-- A nonintegral rational phase has nearest integer distance at least inverse denominator.
Source: P0013 page 45, separation argument for equation 4.38. -/
theorem rational_noninteger_distance707 (a : ℤ) (q : ℕ) (hq : 0 < q)
    (ha : ¬ (q : ℤ) ∣ a) :
    1 / (q : ℝ) ≤ |(a : ℝ) / q - round ((a : ℝ) / q)| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hne : a - round ((a : ℝ) / q) * (q : ℤ) ≠ 0 := by
    intro he
    apply ha
    rw [sub_eq_zero.mp he]
    exact dvd_mul_left _ _
  have hd : (1 : ℝ) ≤ |(a : ℝ) - (round ((a : ℝ) / q) : ℝ) * q| := by
    exact_mod_cast Int.one_le_abs hne
  have heq : |(a : ℝ) / q - round ((a : ℝ) / q)| * q =
      |(a : ℝ) - (round ((a : ℝ) / q) : ℝ) * q| := by
    calc
      _ = |(a : ℝ) / q - round ((a : ℝ) / q)| * |(q : ℝ)| := by rw [abs_of_pos hq0]
      _ = |((a : ℝ) / q - round ((a : ℝ) / q)) * q| := (abs_mul _ _).symm
      _ = _ := by congr 1; field_simp
  apply (div_le_iff₀ hq0).mpr
  rw [heq]
  exact hd

example := rational_noninteger_distance707 1 3 (by norm_num) (by norm_num)

/-- A perturbation of a nonintegral rational phase retains its separation budget.
Source: P0013 page 45, separation argument for equation 4.38. -/
theorem perturbed_rational_distance707 (θ u ν : ℝ) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (ha : ¬ (q : ℤ) ∣ a)
    (herror : |θ - (a : ℝ) / q| ≤ u) (hbudget : ν + u ≤ 1 / (q : ℝ)) :
    ν ≤ |θ - round θ| := by
  have hg := rational_noninteger_distance707 a q hq ha
  have hs := nearest_distance_stable252 θ ((a : ℝ) / q)
  linarith

example := perturbed_rational_distance707 (1 / 3) 0 (1 / 3) 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The rational frequency clusters of Lemma 4.3 remain separated modulo one.
Source: P0013 page 45, separation argument for equation 4.38. -/
theorem rational_cluster_separation707 (s : Finset ℕ) (a : ℕ → ℤ) (v : ℕ → ℝ)
    (q : ℕ) (hq : 0 < q) (ν u : ℝ)
    (hres : ∀ i ∈ s, ∀ j ∈ s, a i ≠ a j → ¬ (q : ℤ) ∣ a i - a j)
    (hwidth : ∀ i ∈ s, ∀ j ∈ s, |v i - v j| ≤ u)
    (hsame : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → a i = a j →
      ν ≤ |v i - v j - round (v i - v j)|)
    (hbudget : ν + u ≤ 1 / (q : ℝ)) :
    ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ν ≤ |((a i : ℝ) / q + v i) - ((a j : ℝ) / q + v j) -
        round (((a i : ℝ) / q + v i) - ((a j : ℝ) / q + v j))| := by
  intro i hi j hj hij
  by_cases he : a i = a j
  · have hh := hsame i hi j hj hij he
    have hid : ((a i : ℝ) / q + v i) - ((a j : ℝ) / q + v j) = v i - v j := by rw [he]; ring
    rwa [hid]
  · apply perturbed_rational_distance707 _ u ν (a i - a j) q hq (hres i hi j hj he) _ hbudget
    have hid : ((a i : ℝ) / q + v i) - ((a j : ℝ) / q + v j) -
        ((a i - a j : ℤ) : ℝ) / q = v i - v j := by push_cast; ring
    rw [hid]
    exact hwidth i hi j hj

example := rational_cluster_separation707 {0, 1} (fun i : ℕ => (i : ℤ))
  (fun _ => (0 : ℝ)) 3 (by norm_num) (1 / 3) 0
  (by
    intro i hi j hj hne
    simp only [mem_insert, mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> norm_num at *)
  (by intros; simp)
  (by
    intro i hi j hj hij he
    have he' : i = j := by exact_mod_cast he
    exact (hij he').elim)
  (by norm_num)

/-- Ordinary spacing and a width budget control distance modulo one.
Source: P0013 page 45, separation argument for equation 4.38. -/
theorem nearest_distance_of_spacing707 (β ν u : ℝ)
    (hlower : ν ≤ |β|) (hupper : |β| ≤ u) (hbudget : ν + u ≤ 1) :
    ν ≤ |β - round β| := by
  by_cases hzero : round β = 0
  · simpa only [hzero, Int.cast_zero, sub_zero] using hlower
  · have hk : (1 : ℝ) ≤ |(round β : ℝ)| := by exact_mod_cast Int.one_le_abs hzero
    have ht : |(round β : ℝ)| ≤ |β| + |β - round β| := by
      calc
        _ = |β - (β - round β)| := by congr 1; ring
        _ ≤ _ := abs_sub _ _
    linarith

example := nearest_distance_of_spacing707 (1 / 4) (1 / 4) (1 / 4) (by norm_num) (by norm_num) (by norm_num)

/-- The interval and numerator hypotheses of Lemma 4.3 imply separation modulo one.
Source: P0013 page 45, separation argument for equation 4.38. -/
theorem rational_cluster_separation_of_interval707 (s : Finset ℕ)
    (a : ℕ → ℤ) (v : ℕ → ℝ) (q : ℕ) (hq : 0 < q) (ν u : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i < (q : ℤ))
    (hwidth : ∀ i ∈ s, ∀ j ∈ s, |v i - v j| ≤ u)
    (hsame : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → a i = a j → ν ≤ |v i - v j|)
    (hbudget : ν + u ≤ 1 / (q : ℝ)) :
    ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ν ≤ |((a i : ℝ) / q + v i) - ((a j : ℝ) / q + v j) -
        round (((a i : ℝ) / q + v i) - ((a j : ℝ) / q + v j))| := by
  have hres : ∀ i ∈ s, ∀ j ∈ s, a i ≠ a j → ¬ (q : ℤ) ∣ a i - a j := by
    intro i hi j hj hne hd
    have hai := ha i hi
    have haj := ha j hj
    rcases le_total (a i) (a j) with he | he
    · have hd' : (q : ℤ) ∣ a j - a i := by simpa only [neg_sub] using dvd_neg.mpr hd
      have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (sub_nonneg.mpr he)
        (by omega : a j - a i < (q : ℤ)) hd'
      exact hne (by omega)
    · have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (sub_nonneg.mpr he)
        (by omega : a i - a j < (q : ℤ)) hd
      exact hne (by omega)
  apply rational_cluster_separation707 s a v q hq ν u hres hwidth _ hbudget
  intro i hi j hj hij he
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Nat.succ_le_of_lt hq)
  have hinv : 1 / (q : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hq1
  exact nearest_distance_of_spacing707 (v i - v j) ν u (hsame i hi j hj hij he)
    (hwidth i hi j hj) (hbudget.trans hinv)

example := rational_cluster_separation_of_interval707 {0, 1} (fun _ : ℕ => (0 : ℤ))
  (fun i : ℕ => (i : ℝ) / 4) 1 (by norm_num) (1 / 4) (1 / 4)
  (by intros; norm_num)
  (by
    intro i hi j hj
    simp only [mem_insert, mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> norm_num)
  (by
    intro i hi j hj hij he
    simp only [mem_insert, mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> norm_num at *)
  (by norm_num)

end LeanLab.HelfgottArcs.Cluster707

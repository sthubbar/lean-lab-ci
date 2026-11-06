/-
Alsetri Proposition 4.1 from the three steps in Shao Section 4.1.
Sources: https://arxiv.org/abs/2505.09648v3 page 12, displays 4.1 to 4.5.
https://arxiv.org/abs/1206.6139v2 pages 13 to 15, Lemmas 4.2 to 4.4.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DensityGoldbach.AlsetriTransfer
import LeanLab.DensityGoldbach.Counting408
import LeanLab.DensityGoldbach.Stability408
import LeanLab.DensityGoldbach.Smoothing408

open Finset

namespace LeanLab.DensityGoldbach.Decomp408a

/-- LEAF. Shao page 14, Lemma 4.2 parts 1 to 4. Green and Tao
math/0405581v2 pages 16 to 18, displays 5.8 to 5.15, prove the Bohr smoothing
bounds. This single function statement has no density or convolution conclusion. -/
theorem smoothing (a ε q M : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hq2 : 2 < q) (hq3 : q < 3) (hM : 0 < M) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N.Prime → N₀ ≤ N → ∀ [NeZero N],
      ∀ ν f : ZMod N → ℝ,
      (∀ x, 0 ≤ f x ∧ f x ≤ ν x) →
      (∀ r, ‖fourierZN N ν r - (if r = 0 then 1 else 0)‖ ≤ η) →
      (∑ r, ‖fourierZN N f r‖ ^ q) ^ (1 / q) ≤ M →
      ∃ g : ZMod N → ℝ,
        (∀ x, 0 ≤ g x ∧ g x ≤ (1 + a) / N) ∧
        (∑ x, g x) = ∑ x, f x ∧
        (∀ r, ‖fourierZN N f r - fourierZN N g r‖ ≤ ε) ∧
        (∑ r, ‖fourierZN N g r‖ ^ q) ^ (1 / q) ≤ M := by
  exact Smoothing408.probability_smoothing a ε q M ha hε hq2 hq3 hM

/-- LEAF. Shao page 14, Lemma 4.3, Fourier inversion and Holder.
Three telescoping terms replace the seven expanded terms. The bound uses
`2 * M` for the Fourier norm of a difference. No density assumption is used. -/
theorem convolution_error {N : ℕ} [NeZero N] (q M ε : ℝ)
    (hq2 : 2 < q) (hq3 : q < 3) (hM : 0 < M) (hε : 0 < ε)
    (f g : Fin 3 → ZMod N → ℝ)
    (hf : ∀ i, (∑ r, ‖fourierZN N (f i) r‖ ^ q) ^ (1 / q) ≤ M)
    (hg : ∀ i, (∑ r, ‖fourierZN N (g i) r‖ ^ q) ^ (1 / q) ≤ M)
    (hclose : ∀ i r, ‖fourierZN N (f i) r - fourierZN N (g i) r‖ ≤ ε)
    (x : ZMod N) :
    |(∑ y : ZMod N, ∑ z : ZMod N, f 0 y * f 1 z * f 2 (x - y - z)) -
      (∑ y : ZMod N, ∑ z : ZMod N, g 0 y * g 1 z * g 2 (x - y - z))| ≤
      3 * (2 * M) ^ q * ε ^ (3 - q) / N := by
  exact Stability408.triple_stability q M ε hq2 hq3 hM hε f g hf hg hclose x

/-- LEAF. Shao page 15, the superlevel sets preceding Lemma 4.4 and the
display following it. Li and Pan math/0701240v3 pages 10 to 11, Lemma 3.3,
provide the quantitative sumset count through Pollard's theorem.
Only bounded dense functions occur. There is no pseudorandom majorant. -/
theorem dense_count (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N.Prime → N₀ ≤ N → ∀ [NeZero N],
      ∀ g : Fin 3 → ZMod N → ℝ,
      (∀ i x, 0 ≤ g i x ∧ g i x ≤ (1 + δ / 10) / N) →
      (∀ i, δ ≤ ∑ x, g i x) →
      δ ≤ (∑ x, g 0 x) + (∑ x, g 1 x) + (∑ x, g 2 x) - 1 →
      ∀ x : ZMod N, c / N ≤
        ∑ y : ZMod N, ∑ z : ZMod N, g 0 y * g 1 z * g 2 (x - y - z) := by
  obtain ⟨N₀, hN₀⟩ := Counting408.popular_triples (δ / 2) (by positivity)
  refine ⟨δ ^ 6 * (δ / 8) ^ 3, by positivity, N₀, ?_⟩
  intro N hNp hN inst g hg hmass htotal
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNp.pos
  let X : Fin 3 → Finset (ZMod N) := fun i => univ.filter (fun x => δ ^ 2 / N ≤ g i x)
  let density : Fin 3 → ℝ := fun i => ((X i).card : ℝ) / N
  have hbd : ∀ i, (∑ x, g i x) ≤ (1 + δ / 10) * density i + δ ^ 2 := by
    intro i
    exact Counting408.superlevel_mass (g i) (1 + δ / 10) (δ ^ 2)
      (by positivity) (by positivity) (fun x => (hg i x).2)
  obtain ⟨hind, hsum⟩ := Counting408.superlevel_densities δ hδ hδsmall
    (fun i => ∑ x, g i x) density hmass (by linarith) hbd
  have hcard : ∀ i, δ / 2 * N ≤ ((X i).card : ℝ) := by
    intro i
    exact (le_div_iff₀ hNpos).mp (hind i)
  have hcardsum : (1 + δ / 2) * N ≤ ((X 0).card : ℝ) + (X 1).card + (X 2).card := by
    have hsum' : 1 + δ / 2 ≤ (((X 0).card : ℝ) + (X 1).card + (X 2).card) / N := by
      simpa only [density, ← add_div] using hsum
    exact (le_div_iff₀ hNpos).mp hsum'
  intro x
  have hcount := hN₀ N hNp hN X hcard hcardsum x
  have hweight := Counting408.weighted_count g (δ ^ 2 / N) (by positivity)
    (fun i x => (hg i x).1) x
  have heq : (((univ : Finset (ZMod N × ZMod N)).filter
      (fun yz => yz.1 ∈ X 0 ∧ yz.2 ∈ X 1 ∧ x - yz.1 - yz.2 ∈ X 2)).card : ℝ) =
      (((univ : Finset (ZMod N × ZMod N)).filter
      (fun yz => δ ^ 2 / N ≤ g 0 yz.1 ∧ δ ^ 2 / N ≤ g 1 yz.2 ∧
        δ ^ 2 / N ≤ g 2 (x - yz.1 - yz.2))).card : ℝ) := by
    simp only [X, mem_filter, mem_univ, true_and]
  rw [heq] at hcount
  have hscaled := mul_le_mul_of_nonneg_left hcount (show 0 ≤ (δ ^ 2 / (N : ℝ)) ^ 3 by positivity)
  have hid : (δ ^ 2 / (N : ℝ)) ^ 3 * ((δ / 2 / 4) ^ 3 * (N : ℝ) ^ 2) =
      (δ ^ 6 * (δ / 8) ^ 3) / N := by
    field_simp
    <;> ring
  rw [hid] at hscaled
  exact hscaled.trans hweight


/-- Shao page 15, final choice of the uniformity parameter after Lemma 4.4.
The error budget is half the positive dense contribution. -/
theorem error_budget (c M q : ℝ) (hc : 0 < c) (hM : 0 < M) (hq : q < 3) :
    ∃ ε : ℝ, 0 < ε ∧ 3 * (2 * M) ^ q * ε ^ (3 - q) = c / 2 := by
  have hpow : 0 < (2 * M) ^ q := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨(c / (6 * (2 * M) ^ q)) ^ (3 - q)⁻¹, by positivity, ?_⟩
  rw [Real.rpow_inv_rpow (by positivity) (by linarith)]
  field_simp
  <;> ring

/-- Exact statement of Alsetri Proposition 4.1, assembled from the three leaves.
CONDITIONAL ON Counting408.popular_triples through dense_count. -/
theorem alsetri_prop_4_1_decomposed : AlsetriProp41 := by
  intro δ hδ
  let d : ℝ := min δ (1 / 8)
  have hd : 0 < d := lt_min hδ (by norm_num)
  have hdδ : d ≤ δ := min_le_left _ _
  have hdsmall : d ≤ 1 / 8 := min_le_right _ _
  obtain ⟨c, hc, Nd, hDense⟩ := dense_count d hd hdsmall
  refine ⟨c / 2, by positivity, ?_⟩
  intro q hq2 hq3 M hM
  obtain ⟨ε, hε, hbudget⟩ := error_budget c M q hc hM hq3
  obtain ⟨η, hη, Ns, hSmooth⟩ := smoothing (d / 10) ε q M (by positivity) hε hq2 hq3 hM
  refine ⟨η, hη, max Nd Ns, ?_⟩
  intro N hNp hN inst ν f hf hmass htotal hν hnorm
  have hs : ∀ i : Fin 3, ∃ g : ZMod N → ℝ,
      (∀ x, 0 ≤ g x ∧ g x ≤ (1 + d / 10) / N) ∧
      (∑ x, g x) = ∑ x, f i x ∧
      (∀ r, ‖fourierZN N (f i) r - fourierZN N g r‖ ≤ ε) ∧
      (∑ r, ‖fourierZN N g r‖ ^ q) ^ (1 / q) ≤ M := by
    intro i
    exact hSmooth N hNp (le_trans (le_max_right _ _) hN) (ν i) (f i)
      (hf i) (hν i) (hnorm i)
  choose g hbound hmean hclose hgnorm using hs
  have hgmean : ∀ i, d ≤ ∑ x, g i x := by
    intro i
    rw [hmean i]
    exact hdδ.trans (hmass i)
  have hgtotal : d ≤ (∑ x, g 0 x) + (∑ x, g 1 x) + (∑ x, g 2 x) - 1 := by
    rw [hmean 0, hmean 1, hmean 2]
    exact hdδ.trans htotal
  intro x
  have hmain := hDense N hNp (le_trans (le_max_left _ _) hN) g hbound hgmean hgtotal x
  have herr := convolution_error q M ε hq2 hq3 hM hε f g hnorm hgnorm hclose x
  rw [hbudget] at herr
  have hdiv : (c / 2) / (N : ℝ) = (c / (N : ℝ)) / 2 := by ring
  rw [hdiv] at herr ⊢
  linarith [neg_abs_le ((∑ y : ZMod N, ∑ z : ZMod N, f 0 y * f 1 z * f 2 (x - y - z)) -
    (∑ y : ZMod N, ∑ z : ZMod N, g 0 y * g 1 z * g 2 (x - y - z)))]

end LeanLab.DensityGoldbach.Decomp408a

#print axioms LeanLab.DensityGoldbach.Decomp408a.error_budget
#print axioms LeanLab.DensityGoldbach.Decomp408a.alsetri_prop_4_1_decomposed

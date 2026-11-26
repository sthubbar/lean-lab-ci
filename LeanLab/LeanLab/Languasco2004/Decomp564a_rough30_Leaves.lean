/-
Jia 1996, Lemma 27, pages 280 and 281, with display 40 and Lemma 21, pages 261, 262 and 270.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
Split of Decomp564a.rough30_to_integral into four OPEN leaves and a proved assembly.
The integrand of inner30 is Buchstab's function omega of s = (1 + log (s - 1)) / s on 2 <= s <= 3,
with p = Y^t, q = Y^u and s = (1 - t - u) / u, so that s - 1 = (1 - t) / u - 2.
The leaves are: the Buchstab count for one pair p, q; the prime double sum as a Riemann sum
of the inner30 integral; a Mertens bound for the reciprocal double sum; and the identification
of region label 30 with the five inequalities of region 30 in Jia's table.
-/
import LeanLab.Languasco2004.Model564
import LeanLab.Languasco2004.Decomp564a_rough30_Mertens

namespace LeanLab.Languasco2004.Decomp564aRoughLeaves
open Finset Real Decomp279a Decomp316a Decomp316c GroupSplit548 Model564 Numeric30_548
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF: Jia page 263 display 48 with the Buchstab asymptotic quoted on page 281, Lemma 27.
Class HARD.
For primes p, q in region 30 of Jia's table, the count of q rough integers a in Y < a <= 2Y
with p q dividing a is at least omega of s times Y / (p q log q), here written as
(1 + log (s - 1)) / log (Y / (p q)) with s = log (Y / (p q)) / log q, up to delta Y / (p q log Y).
On region 30, s lies near 2.87, inside 2 <= s <= 3 where omega has this closed form. -/
theorem leaf_buchstab_region30 (δ : ℝ) (hδ : 0 < δ) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∀ p q : ℕ, p.Prime → q.Prime →
      (Y ^ (34 / 99 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (1649 / 4752 : ℝ) ∧
        (p : ℝ) ^ (-2 : ℝ) * Y ^ (85 / 99 : ℝ) < (q : ℝ) ∧
        (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * Y ^ (85 / 147 : ℝ)) →
      Y / ((p : ℝ) * q) *
          ((1 + Real.log (Real.log (Y / ((p : ℝ) * q)) / Real.log q - 1)) /
            Real.log (Y / ((p : ℝ) * q)))
        - δ * Y / ((p : ℝ) * q * Real.log Y) ≤ (roughCount Y (p * q) q : ℝ) := by
  sorry

/-- LEAF: Jia page 281, Lemma 27, the prime number theorem applied twice to the region 30 sum.
Class HARD.
With p = Y^t and q = Y^u, the double sum over primes of the Buchstab weight divided by p q is a
Riemann sum for the source integral inner30 over 34/99 <= t <= 1649/4752, divided by log Y. -/
theorem leaf_prime_sum_region30 (δ : ℝ) (hδ : 0 < δ) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ((∫ t in (34 / 99 : ℝ)..(1649 / 4752), inner30 t) - δ) / Real.log Y ≤
        ∑ p ∈ range (⌊2 * Y⌋₊ + 1), ∑ q ∈ range (⌊2 * Y⌋₊ + 1),
          if p.Prime ∧ q.Prime ∧
            (Y ^ (34 / 99 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (1649 / 4752 : ℝ) ∧
              (p : ℝ) ^ (-2 : ℝ) * Y ^ (85 / 99 : ℝ) < (q : ℝ) ∧
              (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * Y ^ (85 / 147 : ℝ))
          then (1 + Real.log (Real.log (Y / ((p : ℝ) * q)) / Real.log q - 1)) /
              Real.log (Y / ((p : ℝ) * q)) / ((p : ℝ) * q)
          else 0 := by
  sorry

/-- LEAF: Jia page 281, Lemma 27, the error term of the Buchstab step summed over region 30.
Class MEDIUM.
The reciprocal double sum over region 30 is bounded, by Mertens' estimate for the sum of 1/p
over Y^a < p <= Y^b, which follows from a Chebyshev upper bound and partial summation.
PROVED S154 from the Mertens window bound of Decomp564a_rough30_Mertens. -/
theorem leaf_reciprocal_sum_region30 :
    ∃ K Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      (∑ p ∈ range (⌊2 * Y⌋₊ + 1), ∑ q ∈ range (⌊2 * Y⌋₊ + 1),
          if p.Prime ∧ q.Prime ∧
            (Y ^ (34 / 99 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (1649 / 4752 : ℝ) ∧
              (p : ℝ) ^ (-2 : ℝ) * Y ^ (85 / 99 : ℝ) < (q : ℝ) ∧
              (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * Y ^ (85 / 147 : ℝ))
          then 1 / ((p : ℝ) * q) else 0) ≤ K := by
  -- PROVED S154 from the Mertens window bound of Decomp564a_rough30_Mertens.
  set a₂ : ℝ := 85 / 99 - 2 * (1649 / 4752) with ha₂
  set b₂ : ℝ := 85 / 147 - 58 / 49 * (34 / 99) with hb₂
  obtain ⟨K₁, Y₁, h1⟩ := Decomp564aRoughMertens.prime_reciprocal_window
    (34 / 99) (1649 / 4752) (by norm_num) (by norm_num)
  obtain ⟨K₂, Y₂, h2⟩ := Decomp564aRoughMertens.prime_reciprocal_window
    a₂ b₂ (by norm_num [ha₂]) (by norm_num [ha₂, hb₂])
  refine ⟨max K₁ 0 * max K₂ 0, max (max Y₁ Y₂) 1, ?_⟩
  intro Y hY
  have hY1 : (1 : ℝ) ≤ Y := (le_max_right _ _).trans hY
  have hY0 : (0 : ℝ) < Y := by linarith
  have hYa : Y₁ ≤ Y := (le_max_left _ _).trans ((le_max_left _ _).trans hY)
  have hYb : Y₂ ≤ Y := (le_max_right _ _).trans ((le_max_left _ _).trans hY)
  set M := ⌊2 * Y⌋₊ + 1
  set f : ℕ → ℝ := fun p =>
    if p.Prime ∧ Y ^ (34 / 99 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (1649 / 4752 : ℝ)
    then 1 / (p : ℝ) else 0 with hf
  set g : ℕ → ℝ := fun q =>
    if q.Prime ∧ Y ^ a₂ < (q : ℝ) ∧ (q : ℝ) ≤ Y ^ b₂ then 1 / (q : ℝ) else 0 with hg
  have hf0 : ∀ p, 0 ≤ f p := by
    intro p; simp only [hf]; split_ifs <;> positivity
  have hg0 : ∀ q, 0 ≤ g q := by
    intro q; simp only [hg]; split_ifs <;> positivity
  have hterm : ∀ p q : ℕ,
      (if p.Prime ∧ q.Prime ∧
          (Y ^ (34 / 99 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (1649 / 4752 : ℝ) ∧
            (p : ℝ) ^ (-2 : ℝ) * Y ^ (85 / 99 : ℝ) < (q : ℝ) ∧
            (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * Y ^ (85 / 147 : ℝ))
        then 1 / ((p : ℝ) * q) else 0) ≤ f p * g q := by
    intro p q
    split_ifs with hc
    · obtain ⟨hp, hq, hR0, hR1, hR2, hR3⟩ := hc
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hYa0 : (0 : ℝ) < Y ^ (34 / 99 : ℝ) := by positivity
      -- lower bound for q
      have hlow : Y ^ a₂ < (q : ℝ) := by
        have e : Y ^ a₂ = (Y ^ (1649 / 4752 : ℝ)) ^ (-2 : ℝ) * Y ^ (85 / 99 : ℝ) := by
          rw [← Real.rpow_mul hY0.le, ← Real.rpow_add hY0, ha₂]; congr 1; ring
        rw [e]
        calc (Y ^ (1649 / 4752 : ℝ)) ^ (-2 : ℝ) * Y ^ (85 / 99 : ℝ)
            ≤ (p : ℝ) ^ (-2 : ℝ) * Y ^ (85 / 99 : ℝ) := by
              gcongr ?_ * _
              exact Real.rpow_le_rpow_of_nonpos hp0 hR1 (by norm_num)
          _ < q := hR2
      -- upper bound for q
      have hup : (q : ℝ) ≤ Y ^ b₂ := by
        have e : Y ^ b₂ = (Y ^ (34 / 99 : ℝ)) ^ (-58 / 49 : ℝ) * Y ^ (85 / 147 : ℝ) := by
          rw [← Real.rpow_mul hY0.le, ← Real.rpow_add hY0, hb₂]; congr 1; ring
        rw [e]
        refine hR3.le.trans ?_
        gcongr ?_ * _
        exact (Real.rpow_lt_rpow_of_neg hYa0 hR0 (by norm_num)).le
      have hfp : f p = 1 / (p : ℝ) := by simp only [hf]; rw [if_pos ⟨hp, hR0, hR1⟩]
      have hgq : g q = 1 / (q : ℝ) := by simp only [hg]; rw [if_pos ⟨hq, hlow, hup⟩]
      rw [hfp, hgq, one_div_mul_one_div]
    · exact mul_nonneg (hf0 p) (hg0 q)
  calc _ ≤ ∑ p ∈ range M, ∑ q ∈ range M, f p * g q :=
        sum_le_sum (fun p _ => sum_le_sum (fun q _ => hterm p q))
    _ = (∑ p ∈ range M, f p) * (∑ q ∈ range M, g q) := by rw [sum_mul_sum]
    _ ≤ max K₁ 0 * max K₂ 0 := by
      apply mul_le_mul ((h1 Y hYa M).trans (le_max_left _ _))
        ((h2 Y hYb M).trans (le_max_left _ _))
        (sum_nonneg (fun q _ => hg0 q)) (le_max_right _ _)

/-- Jia page 269 table: rows 1 to 28 have p range ending at or below Y^(34/99). -/
private lemma row_upper_le (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 28) :
    ((regionData n 1 : ℚ) : ℝ) ≤ 34 / 99 := by
  have : (regionData n 1 : ℚ) ≤ 34 / 99 := by
    interval_cases n <;> simp [regionData] <;> norm_num
  calc ((regionData n 1 : ℚ) : ℝ) ≤ ((34 / 99 : ℚ) : ℝ) := by exact_mod_cast this
    _ = 34 / 99 := by norm_num

/-- Jia page 269 table, row 29 entry e. -/
private lemma row29_4 : ((regionData 29 4 : ℚ) : ℝ) = -58 / 67 := by
  simp only [regionData]; norm_num

/-- Jia page 269 table, row 29 entry f. -/
private lemma row29_5 : ((regionData 29 5 : ℚ) : ℝ) = 89 / 201 := by
  simp only [regionData]; norm_num

/-- LEAF: Jia pages 269 and 280, the table of regions, row 30, and the first matching label rule.
Class MEDIUM.
For Y at least 2 and primes p, q, the first table row containing p, q is row 30 exactly when
p, q satisfy the row 30 inequalities, that is no row 1 to 29 meets row 30.
This is a finite check of linear inequalities in t = log p / log Y and u = log q / log Y.
PROVED S154: rows 1 to 28 end at p at most Y^(34/99); row 29 is disjoint from row 30 since
row 30 forces log p above 0.366 log Y while p is at most Y^(1649/4752). -/
theorem leaf_regionIndex_eq_30_iff (Y : ℝ) (hY : 2 ≤ Y) (p q : ℕ) (hp : p.Prime)
    (hq : q.Prime) :
    regionIndex Y p q ∈ ({30} : Finset ℕ) ↔
      (Y ^ (34 / 99 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (1649 / 4752 : ℝ) ∧
        (p : ℝ) ^ (-2 : ℝ) * Y ^ (85 / 99 : ℝ) < (q : ℝ) ∧
        (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * Y ^ (85 / 147 : ℝ)) := by
  set P : ℕ → Prop := fun i => i ∈ Icc 1 69 ∧
      Y ^ ((regionData i 0 : ℚ) : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ ((regionData i 1 : ℚ) : ℝ) ∧
      (p : ℝ) ^ ((regionData i 2 : ℚ) : ℝ) * Y ^ ((regionData i 3 : ℚ) : ℝ) < (q : ℝ) ∧
      (q : ℝ) < (p : ℝ) ^ ((regionData i 4 : ℚ) : ℝ) * Y ^ ((regionData i 5 : ℚ) : ℝ) with hP
  have e30 : P 30 ↔
      (Y ^ (34 / 99 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (1649 / 4752 : ℝ) ∧
        (p : ℝ) ^ (-2 : ℝ) * Y ^ (85 / 99 : ℝ) < (q : ℝ) ∧
        (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * Y ^ (85 / 147 : ℝ)) := by
    simp only [hP, regionData]
    norm_num
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hLY : 0 < Real.log Y := Real.log_pos (by linarith)
  rw [Finset.mem_singleton]
  unfold regionIndex
  constructor
  · intro h
    split_ifs at h with hex
    · have hs := Nat.find_spec hex
      rw [h] at hs
      exact e30.mp hs
  · intro hR
    have hex : ∃ i, P i := ⟨30, e30.mpr hR⟩
    simp only [hP] at hex
    rw [dif_pos hex, Nat.find_eq_iff]
    refine ⟨e30.mpr hR, fun n hn hPn => ?_⟩
    obtain ⟨hmem, hn0, hn1, hn2, hn3⟩ := hPn
    have hn1' : 1 ≤ n := (Finset.mem_Icc.mp hmem).1
    obtain ⟨hR0, hR1, hR2, hR3⟩ := hR
    by_cases h28 : n ≤ 28
    · have hb := row_upper_le n hn1' h28
      have : Y ^ ((regionData n 1 : ℚ) : ℝ) ≤ Y ^ (34 / 99 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hY1 hb
      linarith
    · have h29 : n = 29 := by omega
      subst h29
      have hq3 : (q : ℝ) < (p : ℝ) ^ (-58 / 67 : ℝ) * Y ^ (89 / 201 : ℝ) := by
        rw [row29_4, row29_5] at hn3; exact hn3
      have hlt : (p : ℝ) ^ (-2 : ℝ) * Y ^ (85 / 99 : ℝ) <
          (p : ℝ) ^ (-58 / 67 : ℝ) * Y ^ (89 / 201 : ℝ) := hR2.trans hq3
      have hlog := Real.log_lt_log (by positivity) hlt
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
        (by positivity), Real.log_rpow hp0, Real.log_rpow hp0, Real.log_rpow hY0,
        Real.log_rpow hY0] at hlog
      have hpl := Real.log_le_log hp0 hR1
      rw [Real.log_rpow hY0] at hpl
      linarith [hlog, hpl, hLY]

/-- Jia pages 261, 262, 270 and 281: the exact statement of Decomp564a.rough30_to_integral,
assembled from the four leaves above. CONDITIONAL ON those leaves; no admission of its own. -/
theorem rough30_to_integral_from_leaves (δ : ℝ) (hδ : 0 < δ) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → 2 ≤ Y →
      ((∫ t in (34 / 99 : ℝ)..(1649 / 4752), inner30 t) - δ) * Y / Real.log Y ≤
        roughModel {30} Y := by
  obtain ⟨K, Y3, hK⟩ := leaf_reciprocal_sum_region30
  set K' : ℝ := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  set δ' : ℝ := δ / 2 / (K' + 1) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hδ'K : δ' * K' ≤ δ / 2 := by
    have h1 : δ' * (K' + 1) = δ / 2 := by
      rw [hδ']; field_simp
    nlinarith
  obtain ⟨Y1, h1⟩ := leaf_buchstab_region30 δ' hδ'0
  obtain ⟨Y2, h2⟩ := leaf_prime_sum_region30 (δ / 2) (by positivity)
  refine ⟨max (max Y1 Y2) Y3, ?_⟩
  intro Y hY hY2
  have hY1 : Y1 ≤ Y := (le_max_left _ _).trans ((le_max_left _ _).trans hY)
  have hY2' : Y2 ≤ Y := (le_max_right _ _).trans ((le_max_left _ _).trans hY)
  have hY3 : Y3 ≤ Y := (le_max_right _ _).trans hY
  have hL : 0 < Real.log Y := Real.log_pos (by linarith)
  have hYpos : 0 < Y := by linarith
  set A : ℝ := Y / Real.log Y with hA
  have hA0 : 0 < A := div_pos hYpos hL
  -- the region condition, abbreviated
  set R : ℕ → ℕ → Prop := fun p q =>
    Y ^ (34 / 99 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (1649 / 4752 : ℝ) ∧
      (p : ℝ) ^ (-2 : ℝ) * Y ^ (85 / 99 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * Y ^ (85 / 147 : ℝ) with hR
  set w : ℕ → ℕ → ℝ := fun p q =>
    (1 + Real.log (Real.log (Y / ((p : ℝ) * q)) / Real.log q - 1)) /
      Real.log (Y / ((p : ℝ) * q)) with hw
  have hmodel : roughModel {30} Y =
      ∑ p ∈ range (⌊2 * Y⌋₊ + 1), ∑ q ∈ range (⌊2 * Y⌋₊ + 1),
        if p.Prime ∧ q.Prime ∧ R p q then (roughCount Y (p * q) q : ℝ) else 0 := by
    unfold roughModel
    refine sum_congr rfl (fun p _ => sum_congr rfl (fun q _ => ?_))
    by_cases hp : p.Prime
    · by_cases hq : q.Prime
      · have := leaf_regionIndex_eq_30_iff Y hY2 p q hp hq
        simp only [hp, hq, true_and, hR]
        exact if_congr this rfl rfl
      · simp [hq]
    · simp [hp]
  have hterm : ∀ p q : ℕ,
      Y * (if p.Prime ∧ q.Prime ∧ R p q then w p q / ((p : ℝ) * q) else 0)
        - δ' * A * (if p.Prime ∧ q.Prime ∧ R p q then 1 / ((p : ℝ) * q) else 0)
        ≤ (if p.Prime ∧ q.Prime ∧ R p q then (roughCount Y (p * q) q : ℝ) else 0) := by
    intro p q
    by_cases hc : p.Prime ∧ q.Prime ∧ R p q
    · rw [if_pos hc, if_pos hc, if_pos hc]
      have hb := h1 Y hY1 p q hc.1 hc.2.1 hc.2.2
      have he : Y * (w p q / ((p : ℝ) * q)) - δ' * A * (1 / ((p : ℝ) * q)) =
          Y / ((p : ℝ) * q) * w p q - δ' * Y / ((p : ℝ) * q * Real.log Y) := by
        rw [hA]; ring
      rw [he]; exact hb
    · rw [if_neg hc, if_neg hc, if_neg hc]; simp
  have hsum := sum_le_sum (fun p (_ : p ∈ range (⌊2 * Y⌋₊ + 1)) =>
    sum_le_sum (fun q (_ : q ∈ range (⌊2 * Y⌋₊ + 1)) => hterm p q))
  simp only [sum_sub_distrib, ← mul_sum] at hsum
  have hS2 := h2 Y hY2'
  have hS3 := hK Y hY3
  set S1 := ∑ p ∈ range (⌊2 * Y⌋₊ + 1), ∑ q ∈ range (⌊2 * Y⌋₊ + 1),
    (if p.Prime ∧ q.Prime ∧ R p q then w p q / ((p : ℝ) * q) else 0) with hS1
  set S2 := ∑ p ∈ range (⌊2 * Y⌋₊ + 1), ∑ q ∈ range (⌊2 * Y⌋₊ + 1),
    (if p.Prime ∧ q.Prime ∧ R p q then 1 / ((p : ℝ) * q) else 0) with hS2d
  have hS3' : S2 ≤ K' := hS3.trans (le_max_left _ _)
  have hYS1 : A * ((∫ t in (34 / 99 : ℝ)..(1649 / 4752), inner30 t) - δ / 2) ≤ Y * S1 := by
    have := mul_le_mul_of_nonneg_left hS2 hYpos.le
    calc A * ((∫ t in (34 / 99 : ℝ)..(1649 / 4752), inner30 t) - δ / 2)
        = Y * (((∫ t in (34 / 99 : ℝ)..(1649 / 4752), inner30 t) - δ / 2) / Real.log Y) := by
          rw [hA]; ring
      _ ≤ Y * S1 := this
  have hgoal : ((∫ t in (34 / 99 : ℝ)..(1649 / 4752), inner30 t) - δ) * Y / Real.log Y =
      A * ((∫ t in (34 / 99 : ℝ)..(1649 / 4752), inner30 t) - δ) := by
    rw [hA]; ring
  rw [hgoal, hmodel]
  have hAK : δ' * A * S2 ≤ A * (δ / 2) := by
    have : δ' * S2 ≤ δ / 2 := (mul_le_mul_of_nonneg_left hS3' hδ'0.le).trans hδ'K
    nlinarith
  linarith

#print axioms leaf_buchstab_region30
#print axioms leaf_prime_sum_region30
#print axioms leaf_reciprocal_sum_region30
#print axioms leaf_regionIndex_eq_30_iff
#print axioms rough30_to_integral_from_leaves
end
end LeanLab.Languasco2004.Decomp564aRoughLeaves

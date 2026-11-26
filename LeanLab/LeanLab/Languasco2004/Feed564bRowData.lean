/-
Jia 1996 pages 267 to 269 and 281 to 282.
Source https://doi.org/10.4064/aa-77-3-207-287.
Printed subdomain membership and the first match facts behind Feed564bRiemann, split out
so that each module builds well under the 8 GB memory guide, session S140.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Feed564bRough

namespace LeanLab.Languasco2004.Feed564bRiemann
open Finset Real Decomp279a Decomp316c Model564 RemainderData564 Feed564bRough
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Pages 281 and 282: membership of the prime pair p, q in printed subdomain i, with
t = log p / log Y in the row interval and u = log q / log Y strictly between the two row
edges, written multiplicatively as in Decomp316c.regionIndex. -/
def rowMem (i : Fin 16) (Y : ℝ) (p q : ℕ) : Prop :=
  Y ^ (numericData i 0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (numericData i 1 : ℝ) ∧
    (p : ℝ) ^ (numericData i 3 : ℝ) * Y ^ (numericData i 2 : ℝ) < (q : ℝ) ∧
    (q : ℝ) < (p : ℝ) ^ (numericData i 5 : ℝ) * Y ^ (numericData i 4 : ℝ)

/-- Pages 267 to 269 display 52: if region j holds in logarithmic form and every earlier
label fails either its upper p bound or its upper q edge, then j is the first matching region. -/
theorem regionIndex_eq_of_logs' (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p)
    (hq0 : (0 : ℝ) < q) (j : ℕ)
    (a1 : (regionData j 0 : ℝ) * Real.log Y < Real.log p)
    (a2 : Real.log p ≤ (regionData j 1 : ℝ) * Real.log Y)
    (a3 : (regionData j 2 : ℝ) * Real.log p + (regionData j 3 : ℝ) * Real.log Y < Real.log q)
    (a4 : Real.log q < (regionData j 4 : ℝ) * Real.log p + (regionData j 5 : ℝ) * Real.log Y)
    (hj : j ∈ Icc 1 69)
    (hlt : ∀ i < j, i = 0 ∨ (regionData i 1 : ℝ) * Real.log Y < Real.log p ∨
      (regionData i 4 : ℝ) * Real.log p + (regionData i 5 : ℝ) * Real.log Y ≤ Real.log q) :
    regionIndex Y p q = j := by
  have hY0 : 0 < Y := by linarith
  have P : j ∈ Icc 1 69 ∧
      Y ^ (regionData j 0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (regionData j 1 : ℝ) ∧
      (p : ℝ) ^ (regionData j 2 : ℝ) * Y ^ (regionData j 3 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < (p : ℝ) ^ (regionData j 4 : ℝ) * Y ^ (regionData j 5 : ℝ) := by
    refine ⟨hj, ?_, ?_, ?_, ?_⟩
    · rw [← Real.log_lt_log_iff (Real.rpow_pos_of_pos hY0 _) hp0, Real.log_rpow hY0]; exact a1
    · rw [← Real.log_le_log_iff hp0 (Real.rpow_pos_of_pos hY0 _), Real.log_rpow hY0]; exact a2
    · rw [← Real.log_lt_log_iff (by positivity) hq0, Real.log_mul (by positivity) (by positivity),
        Real.log_rpow hp0, Real.log_rpow hY0]; exact a3
    · rw [← Real.log_lt_log_iff hq0 (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_rpow hp0, Real.log_rpow hY0]; exact a4
  unfold regionIndex
  rw [dif_pos ⟨j, P⟩, Nat.find_eq_iff]
  refine ⟨P, fun i hi hPi => ?_⟩
  rcases hlt i hi with h0 | hb | hq
  · subst h0; simp at hPi
  · have := Real.log_le_log hp0 hPi.2.2.1
    rw [Real.log_rpow hY0] at this
    linarith
  · have := Real.log_lt_log hq0 hPi.2.2.2.2
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hp0, Real.log_rpow hY0] at this
    linarith

/-- Pages 281 and 282: membership in printed subdomain i in logarithmic form. -/
theorem rowMem_logs (i : Fin 16) (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p)
    (hq0 : (0 : ℝ) < q) (h : rowMem i Y p q) :
    (numericData i 0 : ℝ) * Real.log Y < Real.log p ∧
      Real.log p ≤ (numericData i 1 : ℝ) * Real.log Y ∧
      (numericData i 3 : ℝ) * Real.log p + (numericData i 2 : ℝ) * Real.log Y < Real.log q ∧
      Real.log q < (numericData i 5 : ℝ) * Real.log p + (numericData i 4 : ℝ) * Real.log Y := by
  have hY0 : 0 < Y := by linarith
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := Real.log_lt_log (Real.rpow_pos_of_pos hY0 _) h1
    rwa [Real.log_rpow hY0] at this
  · have := Real.log_le_log hp0 h2
    rwa [Real.log_rpow hY0] at this
  · have := Real.log_lt_log (by positivity) h3
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_rpow hp0,
      Real.log_rpow hY0] at this
  · have := Real.log_lt_log hq0 h4
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_rpow hp0,
      Real.log_rpow hY0] at this

/-- Jia page 261 display 40: the Buchstab function is positive from 1 on. -/
theorem isBuchstab_nonneg (w : ℝ → ℝ) (hw : IsBuchstab w) (s : ℝ) (hs : 1 ≤ s) : 0 ≤ w s := by
  have hw' := hw
  obtain ⟨_, h12, hdelay⟩ := hw'
  by_cases h2 : s ≤ 2
  · rw [h12 s hs h2]; positivity
  by_cases h3 : s ≤ 3
  · have hd := hdelay s (by linarith)
    have hint : 0 ≤ ∫ x in (1 : ℝ)..(s - 1), w x := by
      apply intervalIntegral.integral_nonneg (by linarith)
      intro x hx
      rw [h12 x hx.1 (by linarith [hx.2])]
      have : (0 : ℝ) < x := by linarith [hx.1]
      positivity
    have : 0 < s * w s := by linarith
    exact (pos_of_mul_pos_right this (by linarith)).le
  · exact le_trans (by norm_num) (buchstab_global_lower w hw s (by linarith))


set_option maxHeartbeats 4000000 in
/-- Pages 267 to 269 and 281: printed subdomain 2 lies in regions 33, 36 under the first match rule. -/
theorem row0_region11 (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p) (hq0 : (0 : ℝ) < q)
    (hm : rowMem 0 Y p q) : regionIndex Y p q ∈ labels11 := by
  obtain ⟨l1, l2, l3, l4⟩ := rowMem_logs 0 Y hY p q hp0 hq0 hm
  simp only [show numericData 0 0 = (1649/4752 : ℚ) from rfl, show numericData 0 1 = (77/221 : ℚ) from rfl, show numericData 0 2 = (34/59 : ℚ) from rfl, show numericData 0 3 = (-70/59 : ℚ) from rfl, show numericData 0 4 = (85/147 : ℚ) from rfl, show numericData 0 5 = (-58/49 : ℚ) from rfl] at l1 l2 l3 l4
  push_cast at l1 l2 l3 l4
  have hL : 0 < Real.log Y := Real.log_pos hY
  by_cases hb0 : Real.log p ≤ (25/72) * Real.log Y
  · rw [regionIndex_eq_of_logs' Y hY p q hp0 hq0 33 ?_ ?_ ?_ ?_ (by simp) ?_]
    · simp [labels11]
    · simp only [show regionData 33 0 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 33 2 = (-70/59 : ℚ) from rfl, show regionData 33 3 = (34/59 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 33 4 = (-58/49 : ℚ) from rfl, show regionData 33 5 = (85/147 : ℚ) from rfl]; push_cast; linarith
    · intro i' hi'
      interval_cases i'
      · exact Or.inl rfl
      · first
          | (right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 1 4 = (1 : ℚ) from rfl, show regionData 1 5 = (0 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 2 4 = (-29/48 : ℚ) from rfl, show regionData 2 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 3 4 = (-29/48 : ℚ) from rfl, show regionData 3 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 4 4 = (1 : ℚ) from rfl, show regionData 4 5 = (0 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 5 4 = (-29/48 : ℚ) from rfl, show regionData 5 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 6 4 = (-1 : ℚ) from rfl, show regionData 6 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 7 4 = (-29/48 : ℚ) from rfl, show regionData 7 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 8 4 = (-1 : ℚ) from rfl, show regionData 8 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 9 4 = (-29/48 : ℚ) from rfl, show regionData 9 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 10 4 = (-1 : ℚ) from rfl, show regionData 10 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 11 4 = (-1/8 : ℚ) from rfl, show regionData 11 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 12 4 = (-29/48 : ℚ) from rfl, show regionData 12 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 13 4 = (-1 : ℚ) from rfl, show regionData 13 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 14 4 = (-1/8 : ℚ) from rfl, show regionData 14 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 15 4 = (-29/48 : ℚ) from rfl, show regionData 15 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 16 4 = (-58/67 : ℚ) from rfl, show regionData 16 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 17 4 = (-1/8 : ℚ) from rfl, show regionData 17 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 18 4 = (-58/67 : ℚ) from rfl, show regionData 18 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 19 4 = (-1/8 : ℚ) from rfl, show regionData 19 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 20 4 = (-58/67 : ℚ) from rfl, show regionData 20 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 21 4 = (-1 : ℚ) from rfl, show regionData 21 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 22 4 = (-58/67 : ℚ) from rfl, show regionData 22 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 23 4 = (-1 : ℚ) from rfl, show regionData 23 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 24 4 = (-58/67 : ℚ) from rfl, show regionData 24 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 25 4 = (-6 : ℚ) from rfl, show regionData 25 5 = (20/9 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 26 4 = (-58/67 : ℚ) from rfl, show regionData 26 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 27 4 = (1/4 : ℚ) from rfl, show regionData 27 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 28 4 = (1/3 : ℚ) from rfl, show regionData 28 5 = (7/54 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 29 4 = (-58/67 : ℚ) from rfl, show regionData 29 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 30 4 = (-58/49 : ℚ) from rfl, show regionData 30 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 31 4 = (1/4 : ℚ) from rfl, show regionData 31 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 32 4 = (-58/67 : ℚ) from rfl, show regionData 32 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
  · have hb0' : (25/72) * Real.log Y < Real.log p := not_le.mp hb0
    rw [regionIndex_eq_of_logs' Y hY p q hp0 hq0 36 ?_ ?_ ?_ ?_ (by simp) ?_]
    · simp [labels11]
    · simp only [show regionData 36 0 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 36 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 36 2 = (-70/59 : ℚ) from rfl, show regionData 36 3 = (34/59 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 36 4 = (-58/49 : ℚ) from rfl, show regionData 36 5 = (85/147 : ℚ) from rfl]; push_cast; linarith
    · intro i' hi'
      interval_cases i'
      · exact Or.inl rfl
      · first
          | (right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 1 4 = (1 : ℚ) from rfl, show regionData 1 5 = (0 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 2 4 = (-29/48 : ℚ) from rfl, show regionData 2 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 3 4 = (-29/48 : ℚ) from rfl, show regionData 3 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 4 4 = (1 : ℚ) from rfl, show regionData 4 5 = (0 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 5 4 = (-29/48 : ℚ) from rfl, show regionData 5 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 6 4 = (-1 : ℚ) from rfl, show regionData 6 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 7 4 = (-29/48 : ℚ) from rfl, show regionData 7 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 8 4 = (-1 : ℚ) from rfl, show regionData 8 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 9 4 = (-29/48 : ℚ) from rfl, show regionData 9 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 10 4 = (-1 : ℚ) from rfl, show regionData 10 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 11 4 = (-1/8 : ℚ) from rfl, show regionData 11 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 12 4 = (-29/48 : ℚ) from rfl, show regionData 12 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 13 4 = (-1 : ℚ) from rfl, show regionData 13 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 14 4 = (-1/8 : ℚ) from rfl, show regionData 14 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 15 4 = (-29/48 : ℚ) from rfl, show regionData 15 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 16 4 = (-58/67 : ℚ) from rfl, show regionData 16 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 17 4 = (-1/8 : ℚ) from rfl, show regionData 17 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 18 4 = (-58/67 : ℚ) from rfl, show regionData 18 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 19 4 = (-1/8 : ℚ) from rfl, show regionData 19 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 20 4 = (-58/67 : ℚ) from rfl, show regionData 20 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 21 4 = (-1 : ℚ) from rfl, show regionData 21 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 22 4 = (-58/67 : ℚ) from rfl, show regionData 22 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 23 4 = (-1 : ℚ) from rfl, show regionData 23 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 24 4 = (-58/67 : ℚ) from rfl, show regionData 24 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 25 4 = (-6 : ℚ) from rfl, show regionData 25 5 = (20/9 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 26 4 = (-58/67 : ℚ) from rfl, show regionData 26 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 27 4 = (1/4 : ℚ) from rfl, show regionData 27 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 28 4 = (1/3 : ℚ) from rfl, show regionData 28 5 = (7/54 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 29 4 = (-58/67 : ℚ) from rfl, show regionData 29 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 30 4 = (-58/49 : ℚ) from rfl, show regionData 30 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 31 4 = (1/4 : ℚ) from rfl, show regionData 31 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 32 4 = (-58/67 : ℚ) from rfl, show regionData 32 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 33 4 = (-58/49 : ℚ) from rfl, show regionData 33 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 34 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 34 4 = (1/4 : ℚ) from rfl, show regionData 34 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 35 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 35 4 = (-58/67 : ℚ) from rfl, show regionData 35 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)

set_option maxHeartbeats 4000000 in
/-- Pages 267 to 269 and 281: printed subdomain 3 lies in regions 36 under the first match rule. -/
theorem row1_region11 (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p) (hq0 : (0 : ℝ) < q)
    (hm : rowMem 1 Y p q) : regionIndex Y p q ∈ labels11 := by
  obtain ⟨l1, l2, l3, l4⟩ := rowMem_logs 1 Y hY p q hp0 hq0 hm
  simp only [show numericData 1 0 = (77/221 : ℚ) from rfl, show numericData 1 1 = (193/549 : ℚ) from rfl, show numericData 1 2 = (34/59 : ℚ) from rfl, show numericData 1 3 = (-70/59 : ℚ) from rfl, show numericData 1 4 = (1/4 : ℚ) from rfl, show numericData 1 5 = (-1/4 : ℚ) from rfl] at l1 l2 l3 l4
  push_cast at l1 l2 l3 l4
  have hL : 0 < Real.log Y := Real.log_pos hY
  rw [regionIndex_eq_of_logs' Y hY p q hp0 hq0 36 ?_ ?_ ?_ ?_ (by simp) ?_]
  · simp [labels11]
  · simp only [show regionData 36 0 = (25/72 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 36 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 36 2 = (-70/59 : ℚ) from rfl, show regionData 36 3 = (34/59 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 36 4 = (-58/49 : ℚ) from rfl, show regionData 36 5 = (85/147 : ℚ) from rfl]; push_cast; linarith
  · intro i' hi'
    interval_cases i'
    · exact Or.inl rfl
    · first
        | (right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 1 4 = (1 : ℚ) from rfl, show regionData 1 5 = (0 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 2 4 = (-29/48 : ℚ) from rfl, show regionData 2 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 3 4 = (-29/48 : ℚ) from rfl, show regionData 3 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 4 4 = (1 : ℚ) from rfl, show regionData 4 5 = (0 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 5 4 = (-29/48 : ℚ) from rfl, show regionData 5 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 6 4 = (-1 : ℚ) from rfl, show regionData 6 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 7 4 = (-29/48 : ℚ) from rfl, show regionData 7 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 8 4 = (-1 : ℚ) from rfl, show regionData 8 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 9 4 = (-29/48 : ℚ) from rfl, show regionData 9 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 10 4 = (-1 : ℚ) from rfl, show regionData 10 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 11 4 = (-1/8 : ℚ) from rfl, show regionData 11 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 12 4 = (-29/48 : ℚ) from rfl, show regionData 12 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 13 4 = (-1 : ℚ) from rfl, show regionData 13 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 14 4 = (-1/8 : ℚ) from rfl, show regionData 14 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 15 4 = (-29/48 : ℚ) from rfl, show regionData 15 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 16 4 = (-58/67 : ℚ) from rfl, show regionData 16 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 17 4 = (-1/8 : ℚ) from rfl, show regionData 17 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 18 4 = (-58/67 : ℚ) from rfl, show regionData 18 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 19 4 = (-1/8 : ℚ) from rfl, show regionData 19 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 20 4 = (-58/67 : ℚ) from rfl, show regionData 20 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 21 4 = (-1 : ℚ) from rfl, show regionData 21 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 22 4 = (-58/67 : ℚ) from rfl, show regionData 22 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 23 4 = (-1 : ℚ) from rfl, show regionData 23 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 24 4 = (-58/67 : ℚ) from rfl, show regionData 24 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 25 4 = (-6 : ℚ) from rfl, show regionData 25 5 = (20/9 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 26 4 = (-58/67 : ℚ) from rfl, show regionData 26 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 27 4 = (1/4 : ℚ) from rfl, show regionData 27 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 28 4 = (1/3 : ℚ) from rfl, show regionData 28 5 = (7/54 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 29 4 = (-58/67 : ℚ) from rfl, show regionData 29 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 30 4 = (-58/49 : ℚ) from rfl, show regionData 30 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 31 4 = (1/4 : ℚ) from rfl, show regionData 31 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 32 4 = (-58/67 : ℚ) from rfl, show regionData 32 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 33 4 = (-58/49 : ℚ) from rfl, show regionData 33 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 34 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 34 4 = (1/4 : ℚ) from rfl, show regionData 34 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 35 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 35 4 = (-58/67 : ℚ) from rfl, show regionData 35 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)

set_option maxHeartbeats 4000000 in
/-- Pages 267 to 269 and 281: printed subdomain 4 lies in regions 36 under the first match rule. -/
theorem row2_region11 (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p) (hq0 : (0 : ℝ) < q)
    (hm : rowMem 2 Y p q) : regionIndex Y p q ∈ labels11 := by
  obtain ⟨l1, l2, l3, l4⟩ := rowMem_logs 2 Y hY p q hp0 hq0 hm
  simp only [show numericData 2 0 = (77/221 : ℚ) from rfl, show numericData 2 1 = (193/549 : ℚ) from rfl, show numericData 2 2 = (1/4 : ℚ) from rfl, show numericData 2 3 = (-1/4 : ℚ) from rfl, show numericData 2 4 = (85/147 : ℚ) from rfl, show numericData 2 5 = (-58/49 : ℚ) from rfl] at l1 l2 l3 l4
  push_cast at l1 l2 l3 l4
  have hL : 0 < Real.log Y := Real.log_pos hY
  rw [regionIndex_eq_of_logs' Y hY p q hp0 hq0 36 ?_ ?_ ?_ ?_ (by simp) ?_]
  · simp [labels11]
  · simp only [show regionData 36 0 = (25/72 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 36 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 36 2 = (-70/59 : ℚ) from rfl, show regionData 36 3 = (34/59 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 36 4 = (-58/49 : ℚ) from rfl, show regionData 36 5 = (85/147 : ℚ) from rfl]; push_cast; linarith
  · intro i' hi'
    interval_cases i'
    · exact Or.inl rfl
    · first
        | (right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 1 4 = (1 : ℚ) from rfl, show regionData 1 5 = (0 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 2 4 = (-29/48 : ℚ) from rfl, show regionData 2 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 3 4 = (-29/48 : ℚ) from rfl, show regionData 3 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 4 4 = (1 : ℚ) from rfl, show regionData 4 5 = (0 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 5 4 = (-29/48 : ℚ) from rfl, show regionData 5 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 6 4 = (-1 : ℚ) from rfl, show regionData 6 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 7 4 = (-29/48 : ℚ) from rfl, show regionData 7 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 8 4 = (-1 : ℚ) from rfl, show regionData 8 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 9 4 = (-29/48 : ℚ) from rfl, show regionData 9 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 10 4 = (-1 : ℚ) from rfl, show regionData 10 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 11 4 = (-1/8 : ℚ) from rfl, show regionData 11 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 12 4 = (-29/48 : ℚ) from rfl, show regionData 12 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 13 4 = (-1 : ℚ) from rfl, show regionData 13 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 14 4 = (-1/8 : ℚ) from rfl, show regionData 14 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 15 4 = (-29/48 : ℚ) from rfl, show regionData 15 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 16 4 = (-58/67 : ℚ) from rfl, show regionData 16 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 17 4 = (-1/8 : ℚ) from rfl, show regionData 17 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 18 4 = (-58/67 : ℚ) from rfl, show regionData 18 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 19 4 = (-1/8 : ℚ) from rfl, show regionData 19 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 20 4 = (-58/67 : ℚ) from rfl, show regionData 20 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 21 4 = (-1 : ℚ) from rfl, show regionData 21 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 22 4 = (-58/67 : ℚ) from rfl, show regionData 22 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 23 4 = (-1 : ℚ) from rfl, show regionData 23 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 24 4 = (-58/67 : ℚ) from rfl, show regionData 24 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 25 4 = (-6 : ℚ) from rfl, show regionData 25 5 = (20/9 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 26 4 = (-58/67 : ℚ) from rfl, show regionData 26 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 27 4 = (1/4 : ℚ) from rfl, show regionData 27 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 28 4 = (1/3 : ℚ) from rfl, show regionData 28 5 = (7/54 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 29 4 = (-58/67 : ℚ) from rfl, show regionData 29 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 30 4 = (-58/49 : ℚ) from rfl, show regionData 30 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 31 4 = (1/4 : ℚ) from rfl, show regionData 31 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 32 4 = (-58/67 : ℚ) from rfl, show regionData 32 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 33 4 = (-58/49 : ℚ) from rfl, show regionData 33 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 34 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 34 4 = (1/4 : ℚ) from rfl, show regionData 34 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 35 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 35 4 = (-58/67 : ℚ) from rfl, show regionData 35 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)

set_option maxHeartbeats 4000000 in
/-- Pages 267 to 269 and 281: printed subdomain 5 lies in regions 36, 38, 40 under the first match rule. -/
theorem row3_region11 (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p) (hq0 : (0 : ℝ) < q)
    (hm : rowMem 3 Y p q) : regionIndex Y p q ∈ labels11 := by
  obtain ⟨l1, l2, l3, l4⟩ := rowMem_logs 3 Y hY p q hp0 hq0 hm
  simp only [show numericData 3 0 = (193/549 : ℚ) from rfl, show numericData 3 1 = (1823/4725 : ℚ) from rfl, show numericData 3 2 = (34/59 : ℚ) from rfl, show numericData 3 3 = (-70/59 : ℚ) from rfl, show numericData 3 4 = (85/147 : ℚ) from rfl, show numericData 3 5 = (-58/49 : ℚ) from rfl] at l1 l2 l3 l4
  push_cast at l1 l2 l3 l4
  have hL : 0 < Real.log Y := Real.log_pos hY
  by_cases hb0 : Real.log p ≤ (10/27) * Real.log Y
  · rw [regionIndex_eq_of_logs' Y hY p q hp0 hq0 36 ?_ ?_ ?_ ?_ (by simp) ?_]
    · simp [labels11]
    · simp only [show regionData 36 0 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 36 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 36 2 = (-70/59 : ℚ) from rfl, show regionData 36 3 = (34/59 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 36 4 = (-58/49 : ℚ) from rfl, show regionData 36 5 = (85/147 : ℚ) from rfl]; push_cast; linarith
    · intro i' hi'
      interval_cases i'
      · exact Or.inl rfl
      · first
          | (right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 1 4 = (1 : ℚ) from rfl, show regionData 1 5 = (0 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 2 4 = (-29/48 : ℚ) from rfl, show regionData 2 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 3 4 = (-29/48 : ℚ) from rfl, show regionData 3 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 4 4 = (1 : ℚ) from rfl, show regionData 4 5 = (0 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 5 4 = (-29/48 : ℚ) from rfl, show regionData 5 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 6 4 = (-1 : ℚ) from rfl, show regionData 6 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 7 4 = (-29/48 : ℚ) from rfl, show regionData 7 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 8 4 = (-1 : ℚ) from rfl, show regionData 8 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 9 4 = (-29/48 : ℚ) from rfl, show regionData 9 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 10 4 = (-1 : ℚ) from rfl, show regionData 10 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 11 4 = (-1/8 : ℚ) from rfl, show regionData 11 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 12 4 = (-29/48 : ℚ) from rfl, show regionData 12 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 13 4 = (-1 : ℚ) from rfl, show regionData 13 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 14 4 = (-1/8 : ℚ) from rfl, show regionData 14 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 15 4 = (-29/48 : ℚ) from rfl, show regionData 15 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 16 4 = (-58/67 : ℚ) from rfl, show regionData 16 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 17 4 = (-1/8 : ℚ) from rfl, show regionData 17 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 18 4 = (-58/67 : ℚ) from rfl, show regionData 18 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 19 4 = (-1/8 : ℚ) from rfl, show regionData 19 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 20 4 = (-58/67 : ℚ) from rfl, show regionData 20 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 21 4 = (-1 : ℚ) from rfl, show regionData 21 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 22 4 = (-58/67 : ℚ) from rfl, show regionData 22 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 23 4 = (-1 : ℚ) from rfl, show regionData 23 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 24 4 = (-58/67 : ℚ) from rfl, show regionData 24 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 25 4 = (-6 : ℚ) from rfl, show regionData 25 5 = (20/9 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 26 4 = (-58/67 : ℚ) from rfl, show regionData 26 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 27 4 = (1/4 : ℚ) from rfl, show regionData 27 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 28 4 = (1/3 : ℚ) from rfl, show regionData 28 5 = (7/54 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 29 4 = (-58/67 : ℚ) from rfl, show regionData 29 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 30 4 = (-58/49 : ℚ) from rfl, show regionData 30 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 31 4 = (1/4 : ℚ) from rfl, show regionData 31 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 32 4 = (-58/67 : ℚ) from rfl, show regionData 32 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 33 4 = (-58/49 : ℚ) from rfl, show regionData 33 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 34 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 34 4 = (1/4 : ℚ) from rfl, show regionData 34 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 35 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 35 4 = (-58/67 : ℚ) from rfl, show regionData 35 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
  · have hb0' : (10/27) * Real.log Y < Real.log p := not_le.mp hb0
    by_cases hb1 : Real.log p ≤ (617/1620) * Real.log Y
    · rw [regionIndex_eq_of_logs' Y hY p q hp0 hq0 38 ?_ ?_ ?_ ?_ (by simp) ?_]
      · simp [labels11]
      · simp only [show regionData 38 0 = (10/27 : ℚ) from rfl]; push_cast; linarith
      · simp only [show regionData 38 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith
      · simp only [show regionData 38 2 = (-70/59 : ℚ) from rfl, show regionData 38 3 = (34/59 : ℚ) from rfl]; push_cast; linarith
      · simp only [show regionData 38 4 = (-58/49 : ℚ) from rfl, show regionData 38 5 = (85/147 : ℚ) from rfl]; push_cast; linarith
      · intro i' hi'
        interval_cases i'
        · exact Or.inl rfl
        · first
            | (right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 1 4 = (1 : ℚ) from rfl, show regionData 1 5 = (0 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 2 4 = (-29/48 : ℚ) from rfl, show regionData 2 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 3 4 = (-29/48 : ℚ) from rfl, show regionData 3 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 4 4 = (1 : ℚ) from rfl, show regionData 4 5 = (0 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 5 4 = (-29/48 : ℚ) from rfl, show regionData 5 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 6 4 = (-1 : ℚ) from rfl, show regionData 6 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 7 4 = (-29/48 : ℚ) from rfl, show regionData 7 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 8 4 = (-1 : ℚ) from rfl, show regionData 8 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 9 4 = (-29/48 : ℚ) from rfl, show regionData 9 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 10 4 = (-1 : ℚ) from rfl, show regionData 10 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 11 4 = (-1/8 : ℚ) from rfl, show regionData 11 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 12 4 = (-29/48 : ℚ) from rfl, show regionData 12 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 13 4 = (-1 : ℚ) from rfl, show regionData 13 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 14 4 = (-1/8 : ℚ) from rfl, show regionData 14 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 15 4 = (-29/48 : ℚ) from rfl, show regionData 15 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 16 4 = (-58/67 : ℚ) from rfl, show regionData 16 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 17 4 = (-1/8 : ℚ) from rfl, show regionData 17 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 18 4 = (-58/67 : ℚ) from rfl, show regionData 18 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 19 4 = (-1/8 : ℚ) from rfl, show regionData 19 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 20 4 = (-58/67 : ℚ) from rfl, show regionData 20 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 21 4 = (-1 : ℚ) from rfl, show regionData 21 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 22 4 = (-58/67 : ℚ) from rfl, show regionData 22 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 23 4 = (-1 : ℚ) from rfl, show regionData 23 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 24 4 = (-58/67 : ℚ) from rfl, show regionData 24 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 25 4 = (-6 : ℚ) from rfl, show regionData 25 5 = (20/9 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 26 4 = (-58/67 : ℚ) from rfl, show regionData 26 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 27 4 = (1/4 : ℚ) from rfl, show regionData 27 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 28 4 = (1/3 : ℚ) from rfl, show regionData 28 5 = (7/54 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 29 4 = (-58/67 : ℚ) from rfl, show regionData 29 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 30 4 = (-58/49 : ℚ) from rfl, show regionData 30 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 31 4 = (1/4 : ℚ) from rfl, show regionData 31 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 32 4 = (-58/67 : ℚ) from rfl, show regionData 32 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 33 4 = (-58/49 : ℚ) from rfl, show regionData 33 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 34 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 34 4 = (1/4 : ℚ) from rfl, show regionData 34 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 35 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 35 4 = (-58/67 : ℚ) from rfl, show regionData 35 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 36 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 36 4 = (-58/49 : ℚ) from rfl, show regionData 36 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 37 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 37 4 = (-23/15 : ℚ) from rfl, show regionData 37 5 = (7/9 : ℚ) from rfl]; push_cast; linarith)
    · have hb1' : (617/1620) * Real.log Y < Real.log p := not_le.mp hb1
      rw [regionIndex_eq_of_logs' Y hY p q hp0 hq0 40 ?_ ?_ ?_ ?_ (by simp) ?_]
      · simp [labels11]
      · simp only [show regionData 40 0 = (617/1620 : ℚ) from rfl]; push_cast; linarith
      · simp only [show regionData 40 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith
      · simp only [show regionData 40 2 = (-70/59 : ℚ) from rfl, show regionData 40 3 = (34/59 : ℚ) from rfl]; push_cast; linarith
      · simp only [show regionData 40 4 = (-58/49 : ℚ) from rfl, show regionData 40 5 = (85/147 : ℚ) from rfl]; push_cast; linarith
      · intro i' hi'
        interval_cases i'
        · exact Or.inl rfl
        · first
            | (right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 1 4 = (1 : ℚ) from rfl, show regionData 1 5 = (0 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 2 4 = (-29/48 : ℚ) from rfl, show regionData 2 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 3 4 = (-29/48 : ℚ) from rfl, show regionData 3 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 4 4 = (1 : ℚ) from rfl, show regionData 4 5 = (0 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 5 4 = (-29/48 : ℚ) from rfl, show regionData 5 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 6 4 = (-1 : ℚ) from rfl, show regionData 6 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 7 4 = (-29/48 : ℚ) from rfl, show regionData 7 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 8 4 = (-1 : ℚ) from rfl, show regionData 8 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 9 4 = (-29/48 : ℚ) from rfl, show regionData 9 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 10 4 = (-1 : ℚ) from rfl, show regionData 10 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 11 4 = (-1/8 : ℚ) from rfl, show regionData 11 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 12 4 = (-29/48 : ℚ) from rfl, show regionData 12 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 13 4 = (-1 : ℚ) from rfl, show regionData 13 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 14 4 = (-1/8 : ℚ) from rfl, show regionData 14 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 15 4 = (-29/48 : ℚ) from rfl, show regionData 15 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 16 4 = (-58/67 : ℚ) from rfl, show regionData 16 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 17 4 = (-1/8 : ℚ) from rfl, show regionData 17 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 18 4 = (-58/67 : ℚ) from rfl, show regionData 18 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 19 4 = (-1/8 : ℚ) from rfl, show regionData 19 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 20 4 = (-58/67 : ℚ) from rfl, show regionData 20 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 21 4 = (-1 : ℚ) from rfl, show regionData 21 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 22 4 = (-58/67 : ℚ) from rfl, show regionData 22 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 23 4 = (-1 : ℚ) from rfl, show regionData 23 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 24 4 = (-58/67 : ℚ) from rfl, show regionData 24 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 25 4 = (-6 : ℚ) from rfl, show regionData 25 5 = (20/9 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 26 4 = (-58/67 : ℚ) from rfl, show regionData 26 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 27 4 = (1/4 : ℚ) from rfl, show regionData 27 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 28 4 = (1/3 : ℚ) from rfl, show regionData 28 5 = (7/54 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 29 4 = (-58/67 : ℚ) from rfl, show regionData 29 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 30 4 = (-58/49 : ℚ) from rfl, show regionData 30 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 31 4 = (1/4 : ℚ) from rfl, show regionData 31 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 32 4 = (-58/67 : ℚ) from rfl, show regionData 32 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 33 4 = (-58/49 : ℚ) from rfl, show regionData 33 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 34 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 34 4 = (1/4 : ℚ) from rfl, show regionData 34 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 35 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 35 4 = (-58/67 : ℚ) from rfl, show regionData 35 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 36 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 36 4 = (-58/49 : ℚ) from rfl, show regionData 36 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 37 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 37 4 = (-23/15 : ℚ) from rfl, show regionData 37 5 = (7/9 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 38 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 38 4 = (-58/49 : ℚ) from rfl, show regionData 38 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
        · first
            | (right; left; simp only [show regionData 39 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith)
            | (right; right; simp only [show regionData 39 4 = (-1 : ℚ) from rfl, show regionData 39 5 = (47/81 : ℚ) from rfl]; push_cast; linarith)

set_option maxHeartbeats 4000000 in
/-- Pages 267 to 269 and 281: printed subdomain 6 lies in regions 42 under the first match rule. -/
theorem row4_region11 (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p) (hq0 : (0 : ℝ) < q)
    (hm : rowMem 4 Y p q) : regionIndex Y p q ∈ labels11 := by
  obtain ⟨l1, l2, l3, l4⟩ := rowMem_logs 4 Y hY p q hp0 hq0 hm
  simp only [show numericData 4 0 = (1823/4725 : ℚ) from rfl, show numericData 4 1 = (3041/7830 : ℚ) from rfl, show numericData 4 2 = (16/135 : ℚ) from rfl, show numericData 4 3 = (0 : ℚ) from rfl, show numericData 4 4 = (85/147 : ℚ) from rfl, show numericData 4 5 = (-58/49 : ℚ) from rfl] at l1 l2 l3 l4
  push_cast at l1 l2 l3 l4
  have hL : 0 < Real.log Y := Real.log_pos hY
  rw [regionIndex_eq_of_logs' Y hY p q hp0 hq0 42 ?_ ?_ ?_ ?_ (by simp) ?_]
  · simp [labels11]
  · simp only [show regionData 42 0 = (1823/4725 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 42 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 42 2 = (0 : ℚ) from rfl, show regionData 42 3 = (16/135 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 42 4 = (-58/49 : ℚ) from rfl, show regionData 42 5 = (85/147 : ℚ) from rfl]; push_cast; linarith
  · intro i' hi'
    interval_cases i'
    · exact Or.inl rfl
    · first
        | (right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 1 4 = (1 : ℚ) from rfl, show regionData 1 5 = (0 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 2 4 = (-29/48 : ℚ) from rfl, show regionData 2 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 3 4 = (-29/48 : ℚ) from rfl, show regionData 3 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 4 4 = (1 : ℚ) from rfl, show regionData 4 5 = (0 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 5 4 = (-29/48 : ℚ) from rfl, show regionData 5 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 6 4 = (-1 : ℚ) from rfl, show regionData 6 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 7 4 = (-29/48 : ℚ) from rfl, show regionData 7 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 8 4 = (-1 : ℚ) from rfl, show regionData 8 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 9 4 = (-29/48 : ℚ) from rfl, show regionData 9 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 10 4 = (-1 : ℚ) from rfl, show regionData 10 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 11 4 = (-1/8 : ℚ) from rfl, show regionData 11 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 12 4 = (-29/48 : ℚ) from rfl, show regionData 12 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 13 4 = (-1 : ℚ) from rfl, show regionData 13 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 14 4 = (-1/8 : ℚ) from rfl, show regionData 14 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 15 4 = (-29/48 : ℚ) from rfl, show regionData 15 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 16 4 = (-58/67 : ℚ) from rfl, show regionData 16 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 17 4 = (-1/8 : ℚ) from rfl, show regionData 17 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 18 4 = (-58/67 : ℚ) from rfl, show regionData 18 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 19 4 = (-1/8 : ℚ) from rfl, show regionData 19 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 20 4 = (-58/67 : ℚ) from rfl, show regionData 20 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 21 4 = (-1 : ℚ) from rfl, show regionData 21 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 22 4 = (-58/67 : ℚ) from rfl, show regionData 22 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 23 4 = (-1 : ℚ) from rfl, show regionData 23 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 24 4 = (-58/67 : ℚ) from rfl, show regionData 24 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 25 4 = (-6 : ℚ) from rfl, show regionData 25 5 = (20/9 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 26 4 = (-58/67 : ℚ) from rfl, show regionData 26 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 27 4 = (1/4 : ℚ) from rfl, show regionData 27 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 28 4 = (1/3 : ℚ) from rfl, show regionData 28 5 = (7/54 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 29 4 = (-58/67 : ℚ) from rfl, show regionData 29 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 30 4 = (-58/49 : ℚ) from rfl, show regionData 30 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 31 4 = (1/4 : ℚ) from rfl, show regionData 31 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 32 4 = (-58/67 : ℚ) from rfl, show regionData 32 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 33 4 = (-58/49 : ℚ) from rfl, show regionData 33 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 34 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 34 4 = (1/4 : ℚ) from rfl, show regionData 34 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 35 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 35 4 = (-58/67 : ℚ) from rfl, show regionData 35 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 36 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 36 4 = (-58/49 : ℚ) from rfl, show regionData 36 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 37 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 37 4 = (-23/15 : ℚ) from rfl, show regionData 37 5 = (7/9 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 38 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 38 4 = (-58/49 : ℚ) from rfl, show regionData 38 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 39 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 39 4 = (-1 : ℚ) from rfl, show regionData 39 5 = (47/81 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 40 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 40 4 = (-58/49 : ℚ) from rfl, show regionData 40 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 41 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 41 4 = (-29/19 : ℚ) from rfl, show regionData 41 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)

set_option maxHeartbeats 4000000 in
/-- Pages 267 to 269 and 281: printed subdomain 7 lies in regions 46 under the first match rule. -/
theorem row5_region11 (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p) (hq0 : (0 : ℝ) < q)
    (hm : rowMem 5 Y p q) : regionIndex Y p q ∈ labels11 := by
  obtain ⟨l1, l2, l3, l4⟩ := rowMem_logs 5 Y hY p q hp0 hq0 hm
  simp only [show numericData 5 0 = (11/27 : ℚ) from rfl, show numericData 5 1 = (121/291 : ℚ) from rfl, show numericData 5 2 = (89/114 : ℚ) from rfl, show numericData 5 3 = (-29/19 : ℚ) from rfl, show numericData 5 4 = (18/23 : ℚ) from rfl, show numericData 5 5 = (-35/23 : ℚ) from rfl] at l1 l2 l3 l4
  push_cast at l1 l2 l3 l4
  have hL : 0 < Real.log Y := Real.log_pos hY
  rw [regionIndex_eq_of_logs' Y hY p q hp0 hq0 46 ?_ ?_ ?_ ?_ (by simp) ?_]
  · simp [labels11]
  · simp only [show regionData 46 0 = (11/27 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 46 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 46 2 = (-29/19 : ℚ) from rfl, show regionData 46 3 = (89/114 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 46 4 = (-35/23 : ℚ) from rfl, show regionData 46 5 = (18/23 : ℚ) from rfl]; push_cast; linarith
  · intro i' hi'
    interval_cases i'
    · exact Or.inl rfl
    · first
        | (right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 1 4 = (1 : ℚ) from rfl, show regionData 1 5 = (0 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 2 4 = (-29/48 : ℚ) from rfl, show regionData 2 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 3 4 = (-29/48 : ℚ) from rfl, show regionData 3 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 4 4 = (1 : ℚ) from rfl, show regionData 4 5 = (0 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 5 4 = (-29/48 : ℚ) from rfl, show regionData 5 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 6 4 = (-1 : ℚ) from rfl, show regionData 6 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 7 4 = (-29/48 : ℚ) from rfl, show regionData 7 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 8 4 = (-1 : ℚ) from rfl, show regionData 8 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 9 4 = (-29/48 : ℚ) from rfl, show regionData 9 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 10 4 = (-1 : ℚ) from rfl, show regionData 10 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 11 4 = (-1/8 : ℚ) from rfl, show regionData 11 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 12 4 = (-29/48 : ℚ) from rfl, show regionData 12 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 13 4 = (-1 : ℚ) from rfl, show regionData 13 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 14 4 = (-1/8 : ℚ) from rfl, show regionData 14 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 15 4 = (-29/48 : ℚ) from rfl, show regionData 15 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 16 4 = (-58/67 : ℚ) from rfl, show regionData 16 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 17 4 = (-1/8 : ℚ) from rfl, show regionData 17 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 18 4 = (-58/67 : ℚ) from rfl, show regionData 18 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 19 4 = (-1/8 : ℚ) from rfl, show regionData 19 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 20 4 = (-58/67 : ℚ) from rfl, show regionData 20 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 21 4 = (-1 : ℚ) from rfl, show regionData 21 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 22 4 = (-58/67 : ℚ) from rfl, show regionData 22 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 23 4 = (-1 : ℚ) from rfl, show regionData 23 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 24 4 = (-58/67 : ℚ) from rfl, show regionData 24 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 25 4 = (-6 : ℚ) from rfl, show regionData 25 5 = (20/9 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 26 4 = (-58/67 : ℚ) from rfl, show regionData 26 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 27 4 = (1/4 : ℚ) from rfl, show regionData 27 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 28 4 = (1/3 : ℚ) from rfl, show regionData 28 5 = (7/54 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 29 4 = (-58/67 : ℚ) from rfl, show regionData 29 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 30 4 = (-58/49 : ℚ) from rfl, show regionData 30 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 31 4 = (1/4 : ℚ) from rfl, show regionData 31 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 32 4 = (-58/67 : ℚ) from rfl, show regionData 32 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 33 4 = (-58/49 : ℚ) from rfl, show regionData 33 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 34 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 34 4 = (1/4 : ℚ) from rfl, show regionData 34 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 35 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 35 4 = (-58/67 : ℚ) from rfl, show regionData 35 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 36 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 36 4 = (-58/49 : ℚ) from rfl, show regionData 36 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 37 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 37 4 = (-23/15 : ℚ) from rfl, show regionData 37 5 = (7/9 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 38 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 38 4 = (-58/49 : ℚ) from rfl, show regionData 38 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 39 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 39 4 = (-1 : ℚ) from rfl, show regionData 39 5 = (47/81 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 40 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 40 4 = (-58/49 : ℚ) from rfl, show regionData 40 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 41 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 41 4 = (-29/19 : ℚ) from rfl, show regionData 41 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 42 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 42 4 = (-58/49 : ℚ) from rfl, show regionData 42 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 43 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 43 4 = (-29/19 : ℚ) from rfl, show regionData 43 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 44 1 = (11/27 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 44 4 = (-29/19 : ℚ) from rfl, show regionData 44 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 45 1 = (34/81 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 45 4 = (-29/19 : ℚ) from rfl, show regionData 45 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)

set_option maxHeartbeats 4000000 in
/-- Pages 267 to 269 and 281: printed subdomain 8 lies in regions 46 under the first match rule. -/
theorem row6_region11 (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p) (hq0 : (0 : ℝ) < q)
    (hm : rowMem 6 Y p q) : regionIndex Y p q ∈ labels11 := by
  obtain ⟨l1, l2, l3, l4⟩ := rowMem_logs 6 Y hY p q hp0 hq0 hm
  simp only [show numericData 6 0 = (121/291 : ℚ) from rfl, show numericData 6 1 = (49/117 : ℚ) from rfl, show numericData 6 2 = (89/114 : ℚ) from rfl, show numericData 6 3 = (-29/19 : ℚ) from rfl, show numericData 6 4 = (1/4 : ℚ) from rfl, show numericData 6 5 = (-1/4 : ℚ) from rfl] at l1 l2 l3 l4
  push_cast at l1 l2 l3 l4
  have hL : 0 < Real.log Y := Real.log_pos hY
  rw [regionIndex_eq_of_logs' Y hY p q hp0 hq0 46 ?_ ?_ ?_ ?_ (by simp) ?_]
  · simp [labels11]
  · simp only [show regionData 46 0 = (11/27 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 46 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 46 2 = (-29/19 : ℚ) from rfl, show regionData 46 3 = (89/114 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 46 4 = (-35/23 : ℚ) from rfl, show regionData 46 5 = (18/23 : ℚ) from rfl]; push_cast; linarith
  · intro i' hi'
    interval_cases i'
    · exact Or.inl rfl
    · first
        | (right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 1 4 = (1 : ℚ) from rfl, show regionData 1 5 = (0 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 2 4 = (-29/48 : ℚ) from rfl, show regionData 2 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 3 4 = (-29/48 : ℚ) from rfl, show regionData 3 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 4 4 = (1 : ℚ) from rfl, show regionData 4 5 = (0 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 5 4 = (-29/48 : ℚ) from rfl, show regionData 5 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 6 4 = (-1 : ℚ) from rfl, show regionData 6 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 7 4 = (-29/48 : ℚ) from rfl, show regionData 7 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 8 4 = (-1 : ℚ) from rfl, show regionData 8 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 9 4 = (-29/48 : ℚ) from rfl, show regionData 9 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 10 4 = (-1 : ℚ) from rfl, show regionData 10 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 11 4 = (-1/8 : ℚ) from rfl, show regionData 11 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 12 4 = (-29/48 : ℚ) from rfl, show regionData 12 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 13 4 = (-1 : ℚ) from rfl, show regionData 13 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 14 4 = (-1/8 : ℚ) from rfl, show regionData 14 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 15 4 = (-29/48 : ℚ) from rfl, show regionData 15 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 16 4 = (-58/67 : ℚ) from rfl, show regionData 16 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 17 4 = (-1/8 : ℚ) from rfl, show regionData 17 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 18 4 = (-58/67 : ℚ) from rfl, show regionData 18 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 19 4 = (-1/8 : ℚ) from rfl, show regionData 19 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 20 4 = (-58/67 : ℚ) from rfl, show regionData 20 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 21 4 = (-1 : ℚ) from rfl, show regionData 21 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 22 4 = (-58/67 : ℚ) from rfl, show regionData 22 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 23 4 = (-1 : ℚ) from rfl, show regionData 23 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 24 4 = (-58/67 : ℚ) from rfl, show regionData 24 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 25 4 = (-6 : ℚ) from rfl, show regionData 25 5 = (20/9 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 26 4 = (-58/67 : ℚ) from rfl, show regionData 26 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 27 4 = (1/4 : ℚ) from rfl, show regionData 27 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 28 4 = (1/3 : ℚ) from rfl, show regionData 28 5 = (7/54 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 29 4 = (-58/67 : ℚ) from rfl, show regionData 29 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 30 4 = (-58/49 : ℚ) from rfl, show regionData 30 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 31 4 = (1/4 : ℚ) from rfl, show regionData 31 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 32 4 = (-58/67 : ℚ) from rfl, show regionData 32 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 33 4 = (-58/49 : ℚ) from rfl, show regionData 33 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 34 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 34 4 = (1/4 : ℚ) from rfl, show regionData 34 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 35 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 35 4 = (-58/67 : ℚ) from rfl, show regionData 35 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 36 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 36 4 = (-58/49 : ℚ) from rfl, show regionData 36 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 37 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 37 4 = (-23/15 : ℚ) from rfl, show regionData 37 5 = (7/9 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 38 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 38 4 = (-58/49 : ℚ) from rfl, show regionData 38 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 39 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 39 4 = (-1 : ℚ) from rfl, show regionData 39 5 = (47/81 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 40 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 40 4 = (-58/49 : ℚ) from rfl, show regionData 40 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 41 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 41 4 = (-29/19 : ℚ) from rfl, show regionData 41 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 42 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 42 4 = (-58/49 : ℚ) from rfl, show regionData 42 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 43 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 43 4 = (-29/19 : ℚ) from rfl, show regionData 43 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 44 1 = (11/27 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 44 4 = (-29/19 : ℚ) from rfl, show regionData 44 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 45 1 = (34/81 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 45 4 = (-29/19 : ℚ) from rfl, show regionData 45 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)

set_option maxHeartbeats 4000000 in
/-- Pages 267 to 269 and 281: printed subdomain 9 lies in regions 46 under the first match rule. -/
theorem row7_region11 (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p) (hq0 : (0 : ℝ) < q)
    (hm : rowMem 7 Y p q) : regionIndex Y p q ∈ labels11 := by
  obtain ⟨l1, l2, l3, l4⟩ := rowMem_logs 7 Y hY p q hp0 hq0 hm
  simp only [show numericData 7 0 = (121/291 : ℚ) from rfl, show numericData 7 1 = (49/117 : ℚ) from rfl, show numericData 7 2 = (1/4 : ℚ) from rfl, show numericData 7 3 = (-1/4 : ℚ) from rfl, show numericData 7 4 = (18/23 : ℚ) from rfl, show numericData 7 5 = (-35/23 : ℚ) from rfl] at l1 l2 l3 l4
  push_cast at l1 l2 l3 l4
  have hL : 0 < Real.log Y := Real.log_pos hY
  rw [regionIndex_eq_of_logs' Y hY p q hp0 hq0 46 ?_ ?_ ?_ ?_ (by simp) ?_]
  · simp [labels11]
  · simp only [show regionData 46 0 = (11/27 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 46 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 46 2 = (-29/19 : ℚ) from rfl, show regionData 46 3 = (89/114 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 46 4 = (-35/23 : ℚ) from rfl, show regionData 46 5 = (18/23 : ℚ) from rfl]; push_cast; linarith
  · intro i' hi'
    interval_cases i'
    · exact Or.inl rfl
    · first
        | (right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 1 4 = (1 : ℚ) from rfl, show regionData 1 5 = (0 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 2 4 = (-29/48 : ℚ) from rfl, show regionData 2 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 3 4 = (-29/48 : ℚ) from rfl, show regionData 3 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 4 4 = (1 : ℚ) from rfl, show regionData 4 5 = (0 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 5 4 = (-29/48 : ℚ) from rfl, show regionData 5 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 6 4 = (-1 : ℚ) from rfl, show regionData 6 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 7 4 = (-29/48 : ℚ) from rfl, show regionData 7 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 8 4 = (-1 : ℚ) from rfl, show regionData 8 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 9 4 = (-29/48 : ℚ) from rfl, show regionData 9 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 10 4 = (-1 : ℚ) from rfl, show regionData 10 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 11 4 = (-1/8 : ℚ) from rfl, show regionData 11 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 12 4 = (-29/48 : ℚ) from rfl, show regionData 12 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 13 4 = (-1 : ℚ) from rfl, show regionData 13 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 14 4 = (-1/8 : ℚ) from rfl, show regionData 14 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 15 4 = (-29/48 : ℚ) from rfl, show regionData 15 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 16 4 = (-58/67 : ℚ) from rfl, show regionData 16 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 17 4 = (-1/8 : ℚ) from rfl, show regionData 17 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 18 4 = (-58/67 : ℚ) from rfl, show regionData 18 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 19 4 = (-1/8 : ℚ) from rfl, show regionData 19 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 20 4 = (-58/67 : ℚ) from rfl, show regionData 20 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 21 4 = (-1 : ℚ) from rfl, show regionData 21 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 22 4 = (-58/67 : ℚ) from rfl, show regionData 22 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 23 4 = (-1 : ℚ) from rfl, show regionData 23 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 24 4 = (-58/67 : ℚ) from rfl, show regionData 24 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 25 4 = (-6 : ℚ) from rfl, show regionData 25 5 = (20/9 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 26 4 = (-58/67 : ℚ) from rfl, show regionData 26 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 27 4 = (1/4 : ℚ) from rfl, show regionData 27 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 28 4 = (1/3 : ℚ) from rfl, show regionData 28 5 = (7/54 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 29 4 = (-58/67 : ℚ) from rfl, show regionData 29 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 30 4 = (-58/49 : ℚ) from rfl, show regionData 30 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 31 4 = (1/4 : ℚ) from rfl, show regionData 31 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 32 4 = (-58/67 : ℚ) from rfl, show regionData 32 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 33 4 = (-58/49 : ℚ) from rfl, show regionData 33 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 34 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 34 4 = (1/4 : ℚ) from rfl, show regionData 34 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 35 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 35 4 = (-58/67 : ℚ) from rfl, show regionData 35 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 36 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 36 4 = (-58/49 : ℚ) from rfl, show regionData 36 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 37 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 37 4 = (-23/15 : ℚ) from rfl, show regionData 37 5 = (7/9 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 38 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 38 4 = (-58/49 : ℚ) from rfl, show regionData 38 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 39 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 39 4 = (-1 : ℚ) from rfl, show regionData 39 5 = (47/81 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 40 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 40 4 = (-58/49 : ℚ) from rfl, show regionData 40 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 41 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 41 4 = (-29/19 : ℚ) from rfl, show regionData 41 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 42 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 42 4 = (-58/49 : ℚ) from rfl, show regionData 42 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 43 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 43 4 = (-29/19 : ℚ) from rfl, show regionData 43 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 44 1 = (11/27 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 44 4 = (-29/19 : ℚ) from rfl, show regionData 44 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)
    · first
        | (right; left; simp only [show regionData 45 1 = (34/81 : ℚ) from rfl]; push_cast; linarith)
        | (right; right; simp only [show regionData 45 4 = (-29/19 : ℚ) from rfl, show regionData 45 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)

set_option maxHeartbeats 4000000 in
/-- Pages 267 to 269 and 281: printed subdomain 10 lies in regions 46, 49 under the first match rule. -/
theorem row8_region11 (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p) (hq0 : (0 : ℝ) < q)
    (hm : rowMem 8 Y p q) : regionIndex Y p q ∈ labels11 := by
  obtain ⟨l1, l2, l3, l4⟩ := rowMem_logs 8 Y hY p q hp0 hq0 hm
  simp only [show numericData 8 0 = (49/117 : ℚ) from rfl, show numericData 8 1 = (49/114 : ℚ) from rfl, show numericData 8 2 = (89/114 : ℚ) from rfl, show numericData 8 3 = (-29/19 : ℚ) from rfl, show numericData 8 4 = (18/23 : ℚ) from rfl, show numericData 8 5 = (-35/23 : ℚ) from rfl] at l1 l2 l3 l4
  push_cast at l1 l2 l3 l4
  have hL : 0 < Real.log Y := Real.log_pos hY
  by_cases hb0 : Real.log p ≤ (34/81) * Real.log Y
  · rw [regionIndex_eq_of_logs' Y hY p q hp0 hq0 46 ?_ ?_ ?_ ?_ (by simp) ?_]
    · simp [labels11]
    · simp only [show regionData 46 0 = (11/27 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 46 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 46 2 = (-29/19 : ℚ) from rfl, show regionData 46 3 = (89/114 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 46 4 = (-35/23 : ℚ) from rfl, show regionData 46 5 = (18/23 : ℚ) from rfl]; push_cast; linarith
    · intro i' hi'
      interval_cases i'
      · exact Or.inl rfl
      · first
          | (right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 1 4 = (1 : ℚ) from rfl, show regionData 1 5 = (0 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 2 4 = (-29/48 : ℚ) from rfl, show regionData 2 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 3 4 = (-29/48 : ℚ) from rfl, show regionData 3 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 4 4 = (1 : ℚ) from rfl, show regionData 4 5 = (0 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 5 4 = (-29/48 : ℚ) from rfl, show regionData 5 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 6 4 = (-1 : ℚ) from rfl, show regionData 6 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 7 4 = (-29/48 : ℚ) from rfl, show regionData 7 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 8 4 = (-1 : ℚ) from rfl, show regionData 8 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 9 4 = (-29/48 : ℚ) from rfl, show regionData 9 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 10 4 = (-1 : ℚ) from rfl, show regionData 10 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 11 4 = (-1/8 : ℚ) from rfl, show regionData 11 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 12 4 = (-29/48 : ℚ) from rfl, show regionData 12 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 13 4 = (-1 : ℚ) from rfl, show regionData 13 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 14 4 = (-1/8 : ℚ) from rfl, show regionData 14 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 15 4 = (-29/48 : ℚ) from rfl, show regionData 15 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 16 4 = (-58/67 : ℚ) from rfl, show regionData 16 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 17 4 = (-1/8 : ℚ) from rfl, show regionData 17 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 18 4 = (-58/67 : ℚ) from rfl, show regionData 18 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 19 4 = (-1/8 : ℚ) from rfl, show regionData 19 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 20 4 = (-58/67 : ℚ) from rfl, show regionData 20 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 21 4 = (-1 : ℚ) from rfl, show regionData 21 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 22 4 = (-58/67 : ℚ) from rfl, show regionData 22 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 23 4 = (-1 : ℚ) from rfl, show regionData 23 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 24 4 = (-58/67 : ℚ) from rfl, show regionData 24 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 25 4 = (-6 : ℚ) from rfl, show regionData 25 5 = (20/9 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 26 4 = (-58/67 : ℚ) from rfl, show regionData 26 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 27 4 = (1/4 : ℚ) from rfl, show regionData 27 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 28 4 = (1/3 : ℚ) from rfl, show regionData 28 5 = (7/54 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 29 4 = (-58/67 : ℚ) from rfl, show regionData 29 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 30 4 = (-58/49 : ℚ) from rfl, show regionData 30 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 31 4 = (1/4 : ℚ) from rfl, show regionData 31 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 32 4 = (-58/67 : ℚ) from rfl, show regionData 32 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 33 4 = (-58/49 : ℚ) from rfl, show regionData 33 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 34 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 34 4 = (1/4 : ℚ) from rfl, show regionData 34 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 35 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 35 4 = (-58/67 : ℚ) from rfl, show regionData 35 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 36 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 36 4 = (-58/49 : ℚ) from rfl, show regionData 36 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 37 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 37 4 = (-23/15 : ℚ) from rfl, show regionData 37 5 = (7/9 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 38 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 38 4 = (-58/49 : ℚ) from rfl, show regionData 38 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 39 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 39 4 = (-1 : ℚ) from rfl, show regionData 39 5 = (47/81 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 40 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 40 4 = (-58/49 : ℚ) from rfl, show regionData 40 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 41 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 41 4 = (-29/19 : ℚ) from rfl, show regionData 41 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 42 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 42 4 = (-58/49 : ℚ) from rfl, show regionData 42 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 43 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 43 4 = (-29/19 : ℚ) from rfl, show regionData 43 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 44 1 = (11/27 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 44 4 = (-29/19 : ℚ) from rfl, show regionData 44 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 45 1 = (34/81 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 45 4 = (-29/19 : ℚ) from rfl, show regionData 45 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)
  · have hb0' : (34/81) * Real.log Y < Real.log p := not_le.mp hb0
    rw [regionIndex_eq_of_logs' Y hY p q hp0 hq0 49 ?_ ?_ ?_ ?_ (by simp) ?_]
    · simp [labels11]
    · simp only [show regionData 49 0 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 49 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 49 2 = (-29/19 : ℚ) from rfl, show regionData 49 3 = (89/114 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 49 4 = (-35/23 : ℚ) from rfl, show regionData 49 5 = (18/23 : ℚ) from rfl]; push_cast; linarith
    · intro i' hi'
      interval_cases i'
      · exact Or.inl rfl
      · first
          | (right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 1 4 = (1 : ℚ) from rfl, show regionData 1 5 = (0 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 2 4 = (-29/48 : ℚ) from rfl, show regionData 2 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 3 4 = (-29/48 : ℚ) from rfl, show regionData 3 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 4 4 = (1 : ℚ) from rfl, show regionData 4 5 = (0 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 5 4 = (-29/48 : ℚ) from rfl, show regionData 5 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 6 4 = (-1 : ℚ) from rfl, show regionData 6 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 7 4 = (-29/48 : ℚ) from rfl, show regionData 7 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 8 4 = (-1 : ℚ) from rfl, show regionData 8 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 9 4 = (-29/48 : ℚ) from rfl, show regionData 9 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 10 4 = (-1 : ℚ) from rfl, show regionData 10 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 11 4 = (-1/8 : ℚ) from rfl, show regionData 11 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 12 4 = (-29/48 : ℚ) from rfl, show regionData 12 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 13 4 = (-1 : ℚ) from rfl, show regionData 13 5 = (16/33 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 14 4 = (-1/8 : ℚ) from rfl, show regionData 14 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 15 4 = (-29/48 : ℚ) from rfl, show regionData 15 5 = (89/288 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 16 4 = (-58/67 : ℚ) from rfl, show regionData 16 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 17 4 = (-1/8 : ℚ) from rfl, show regionData 17 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 18 4 = (-58/67 : ℚ) from rfl, show regionData 18 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 19 4 = (-1/8 : ℚ) from rfl, show regionData 19 5 = (7/24 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 20 4 = (-58/67 : ℚ) from rfl, show regionData 20 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 21 4 = (-1 : ℚ) from rfl, show regionData 21 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 22 4 = (-58/67 : ℚ) from rfl, show regionData 22 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 23 4 = (-1 : ℚ) from rfl, show regionData 23 5 = (113/198 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 24 4 = (-58/67 : ℚ) from rfl, show regionData 24 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 25 4 = (-6 : ℚ) from rfl, show regionData 25 5 = (20/9 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 26 4 = (-58/67 : ℚ) from rfl, show regionData 26 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 27 4 = (1/4 : ℚ) from rfl, show regionData 27 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 28 4 = (1/3 : ℚ) from rfl, show regionData 28 5 = (7/54 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 29 4 = (-58/67 : ℚ) from rfl, show regionData 29 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 30 4 = (-58/49 : ℚ) from rfl, show regionData 30 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 31 4 = (1/4 : ℚ) from rfl, show regionData 31 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 32 4 = (-58/67 : ℚ) from rfl, show regionData 32 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 33 4 = (-58/49 : ℚ) from rfl, show regionData 33 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 34 1 = (25/72 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 34 4 = (1/4 : ℚ) from rfl, show regionData 34 5 = (1/8 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 35 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 35 4 = (-58/67 : ℚ) from rfl, show regionData 35 5 = (89/201 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 36 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 36 4 = (-58/49 : ℚ) from rfl, show regionData 36 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 37 1 = (10/27 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 37 4 = (-23/15 : ℚ) from rfl, show regionData 37 5 = (7/9 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 38 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 38 4 = (-58/49 : ℚ) from rfl, show regionData 38 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 39 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 39 4 = (-1 : ℚ) from rfl, show regionData 39 5 = (47/81 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 40 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 40 4 = (-58/49 : ℚ) from rfl, show regionData 40 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 41 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 41 4 = (-29/19 : ℚ) from rfl, show regionData 41 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 42 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 42 4 = (-58/49 : ℚ) from rfl, show regionData 42 5 = (85/147 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 43 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 43 4 = (-29/19 : ℚ) from rfl, show regionData 43 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 44 1 = (11/27 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 44 4 = (-29/19 : ℚ) from rfl, show regionData 44 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 45 1 = (34/81 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 45 4 = (-29/19 : ℚ) from rfl, show regionData 45 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 46 1 = (34/81 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 46 4 = (-35/23 : ℚ) from rfl, show regionData 46 5 = (18/23 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 47 1 = (34/81 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 47 4 = (-1/4 : ℚ) from rfl, show regionData 47 5 = (25/72 : ℚ) from rfl]; push_cast; linarith)
      · first
          | (right; left; simp only [show regionData 48 1 = (49/114 : ℚ) from rfl]; push_cast; linarith)
          | (right; right; simp only [show regionData 48 4 = (-29/19 : ℚ) from rfl, show regionData 48 5 = (89/114 : ℚ) from rfl]; push_cast; linarith)

#print axioms rowMem
#print axioms regionIndex_eq_of_logs'
#print axioms rowMem_logs
#print axioms isBuchstab_nonneg
#print axioms row0_region11
#print axioms row1_region11
#print axioms row2_region11
#print axioms row3_region11
#print axioms row4_region11
#print axioms row5_region11
#print axioms row6_region11
#print axioms row7_region11
#print axioms row8_region11
end
end LeanLab.Languasco2004.Feed564bRiemann

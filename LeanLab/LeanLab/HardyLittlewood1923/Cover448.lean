import LeanLab.HardyLittlewood1923.Geometry448
import Mathlib.Data.Rat.Lemmas

/-!
AI wrote this Lean code for CODEX task448.
P0004 pages 5 and 6 section 1.4, the joined extreme intervals.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Cover448
open Real Finset
open LeanLab.HardyLittlewood1923.Decomp276a

/-- P0004 pages 5 and 6 section 1.4. Every nonnegative Farey point below one has a reduced natural numerator and a bounded positive denominator. -/
theorem point_representation {N : ℕ} {r : ℚ} (hr : r ∈ fareyPoints N)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ p q : ℕ, 1 ≤ q ∧ q ≤ N ∧ p < q ∧ p.Coprime q ∧ (p : ℚ) / q = r := by
  let p := r.num.toNat
  have hn : (p : ℤ) = r.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hr0)
  have hc : p.Coprime r.den := by
    have h := r.reduced
    rw [← hn] at h
    simpa only [Int.natAbs_natCast] using h
  have hp : (p : ℚ) / r.den = r := by
    have hnQ : (p : ℚ) = r.num := by exact_mod_cast hn
    rw [hnQ, r.num_div_den]
  have hqQ : (0 : ℚ) < r.den := by exact_mod_cast r.pos
  have hlt : p < r.den := by
    have hltQ := (div_lt_one hqQ).mp (show (p : ℚ) / r.den < 1 by rw [hp]; exact hr1)
    exact_mod_cast hltQ
  exact ⟨p, r.den, r.pos, Decomp296Farey.fareyPoints_den_le hr, hlt, hc, hp⟩

/-- P0004 pages 5 and 6 section 1.4. The mediant is the denominator weighted average of its two fractions. -/
theorem mediant_weighted (r s : ℚ) :
    mediant r s = (r * r.den + s * s.den) / (r.den + s.den : ℕ) := by
  have hr : (r.num : ℚ) = r * r.den := (div_eq_iff (by exact_mod_cast r.den_nz)).mp r.num_div_den
  have hs : (s.num : ℚ) = s * s.den := (div_eq_iff (by exact_mod_cast s.den_nz)).mp s.num_div_den
  simp only [mediant, Int.cast_add, hr, hs]

/-- P0004 pages 5 and 6 section 1.4. Adding one to both fractions adds one to their mediant. -/
theorem mediant_add_one (r s : ℚ) : mediant (r + 1) (s + 1) = mediant r s + 1 := by
  have hr : (r + 1).den = r.den := by simpa using Rat.add_natCast_den r 1
  have hs : (s + 1).den = s.den := by simpa using Rat.add_natCast_den s 1
  rw [mediant_weighted, mediant_weighted, hr, hs]
  have hd : ((r.den + s.den : ℕ) : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring


/-- P0004 pages 5 and 6 section 1.4. The predecessor of one is one plus the predecessor of zero. -/
theorem prev_one_shift {N : ℕ} (hN : 1 ≤ N) : fareyPrev N 1 = fareyPrev N 0 + 1 := by
  have hzero : (0 : ℚ) ∈ fareyPoints N := by
    simpa using Geometry448.center_mem (p := 0) (q := 1) (by norm_num) hN (by norm_num) (by norm_num)
  have hone : (1 : ℚ) ∈ fareyPoints N :=
    Decomp354h.farey_mem_of_den (by simpa using hN) (by norm_num) (by norm_num)
  have hminus := (Decomp296Farey.fareyPoints_extremes hN).1
  obtain ⟨hp0, _, hd0, _⟩ := Decomp296Farey.farey_neighbors hN (r := 0) (by norm_num) (by norm_num)
  obtain ⟨hp1, _, hd1, _⟩ := Decomp296Farey.farey_neighbors hN (r := 1) (by norm_num) (by norm_num)
  have hb0 := Decomp354h.farey_prev_max hminus (by norm_num : (-1 : ℚ) < 0)
  have hb1 := Decomp354h.farey_prev_max hzero (by norm_num : (0 : ℚ) < 1)
  have hshift0 : fareyPrev N 0 + 1 ∈ fareyPoints N :=
    Decomp354h.farey_mem_of_den (by simpa using hd0) (by linarith) (by linarith)
  have hshift1 : fareyPrev N 1 - 1 ∈ fareyPoints N :=
    Decomp354h.farey_mem_of_den (by simpa using hd1) (by linarith) (by linarith)
  have h1 := Decomp354h.farey_prev_max hshift0 (by linarith : fareyPrev N 0 + 1 < 1)
  have h2 := Decomp354h.farey_prev_max hshift1 (by linarith : fareyPrev N 1 - 1 < 0)
  linarith

/-- P0004 pages 5 and 6 section 1.4. The left boundary at one is one plus the left boundary at zero. -/
theorem boundary_period {N : ℕ} (hN : 1 ≤ N) :
    mediant (fareyPrev N 1) 1 = mediant (fareyPrev N 0) 0 + 1 := by
  rw [prev_one_shift hN]
  simpa using mediant_add_one (fareyPrev N 0) 0

/-- P0004 pages 5 and 6 section 1.4. The predecessor of the selected successor is the original Farey center. -/
theorem prev_next {N : ℕ} (hN : 1 ≤ N) {r : ℚ}
    (hr : r ∈ fareyPoints N) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    fareyPrev N (fareyNext N r) = r := by
  have hone : (1 : ℚ) ∈ fareyPoints N :=
    Decomp354h.farey_mem_of_den (by simpa using hN) (by norm_num) (by norm_num)
  have hnext := (Decomp296Farey.farey_neighbors hN hr0 hr1.le).2.1
  have hnext1 := Decomp354h.farey_next_min hone hr1
  have hnext0 : 0 ≤ fareyNext N r := hr0.trans hnext.le
  have hprev := (Decomp296Farey.farey_neighbors hN hnext0 hnext1).1
  have hge := Decomp354h.farey_prev_max hr hnext
  apply le_antisymm _ hge
  by_contra hh
  have hh' : r < fareyPrev N (fareyNext N r) := lt_of_not_ge hh
  have hm := Decomp354h.farey_next_min (Geometry448.prev_mem hr hnext) hh'
  exact (not_le_of_gt hprev) hm

set_option maxHeartbeats 1000000 in
/-- P0004 pages 5 and 6 section 1.4. The half open rational cells cover exactly one period after the extreme intervals are joined. -/
theorem rational_cover {N : ℕ} (hN : 1 ≤ N) :
    (⋃ r ∈ (fareyPoints N).filter (fun r => 0 ≤ r ∧ r < 1),
      Set.Ioc (mediant (fareyPrev N r) r : ℝ) (mediant r (fareyNext N r) : ℝ)) =
    Set.Ioc (mediant (fareyPrev N 0) 0 : ℝ) ((mediant (fareyPrev N 0) 0 : ℝ) + 1) := by
  classical
  have hzero : (0 : ℚ) ∈ fareyPoints N := by
    simpa using Geometry448.center_mem (p := 0) (q := 1) (by norm_num) hN (by norm_num) (by norm_num)
  have hone : (1 : ℚ) ∈ fareyPoints N :=
    Decomp354h.farey_mem_of_den (by simpa using hN) (by norm_num) (by norm_num)
  have hneigh := Decomp296Farey.farey_neighbors hN (r := 0) (by norm_num) (by norm_num)
  have hL0 := (Geometry448.mediant_strict hneigh.1).2
  have hR0 := (Geometry448.mediant_strict hneigh.2.1).1
  ext x
  constructor
  · intro hx
    obtain ⟨r, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hr, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hrF, hr0, hr1⟩ := mem_filter.mp hr
    have hlower : (mediant (fareyPrev N 0) 0 : ℝ) ≤ mediant (fareyPrev N r) r := by
      rcases hr0.eq_or_lt with he | hlt
      · subst r; exact le_refl _
      · have hm := Geometry448.mediant_order hN hzero hrF (by norm_num) hr1.le hlt
        exact_mod_cast (show mediant (fareyPrev N 0) 0 ≤ mediant (fareyPrev N r) r by linarith)
    have hupper : (mediant r (fareyNext N r) : ℝ) ≤ (mediant (fareyPrev N 0) 0 : ℝ) + 1 := by
      have hm := Geometry448.mediant_order hN hrF hone hr0 (le_refl 1) hr1
      rw [boundary_period hN] at hm
      exact_mod_cast hm
    exact ⟨hlower.trans_lt hx.1, hx.2.trans hupper⟩
  · intro hx
    let c := (fareyPoints N).filter (fun r => 0 ≤ r ∧ r < 1 ∧ (mediant (fareyPrev N r) r : ℝ) < x)
    have hc : c.Nonempty := ⟨0, mem_filter.mpr ⟨hzero, by norm_num, by norm_num, hx.1⟩⟩
    let r := c.max' hc
    have hrmem : r ∈ c := max'_mem c hc
    obtain ⟨hrF, hr0, hr1, hrL⟩ := mem_filter.mp hrmem
    have hnext := (Decomp296Farey.farey_neighbors hN hr0 hr1.le).2.1
    have hsF := Geometry448.next_mem hone hr1
    have hs1 := Decomp354h.farey_next_min hone hr1
    have hs0 : 0 ≤ fareyNext N r := hr0.trans hnext.le
    have hpn := prev_next hN hrF hr0 hr1
    have hright : x ≤ (mediant r (fareyNext N r) : ℝ) := by
      by_contra hbad
      have hbad' : (mediant r (fareyNext N r) : ℝ) < x := lt_of_not_ge hbad
      rcases hs1.eq_or_lt with he | hlt
      · rw [he] at hpn hbad'
        rw [← hpn, boundary_period hN] at hbad'
        push_cast at hbad'
        exact (not_lt_of_ge hx.2) hbad'
      · have hsL : (mediant (fareyPrev N (fareyNext N r)) (fareyNext N r) : ℝ) < x := by
          rw [hpn]; exact hbad'
        have hsc : fareyNext N r ∈ c := mem_filter.mpr ⟨hsF, hs0, hlt, hsL⟩
        have hle : fareyNext N r ≤ r := le_max' c _ hsc
        exact (not_le_of_gt hnext) hle
    exact Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr
      ⟨mem_filter.mpr ⟨hrF, hr0, hr1⟩, ⟨hrL, hright⟩⟩⟩

#print axioms point_representation
#print axioms mediant_weighted
#print axioms mediant_add_one
#print axioms prev_one_shift
#print axioms boundary_period
#print axioms prev_next
#print axioms rational_cover
end LeanLab.HardyLittlewood1923.Cover448

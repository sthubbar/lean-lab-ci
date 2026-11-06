import LeanLab.HardyLittlewood1923.Decomp354h

/-!
AI wrote this Lean code for CODEX task448.
P0004 pages 5 and 6 section 1.4.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Geometry448
open Real Finset
open LeanLab.HardyLittlewood1923.Decomp276a

/-- P0004 pages 5 and 6 section 1.4. The denominator of a reduced natural fraction is its given denominator. -/
theorem center_den {p q : ℕ} (hq : 1 ≤ q) (hpq : p.Coprime q) :
    ((p : ℚ) / q).den = q := by
  have h := Rat.den_div_eq_of_coprime (a := (p : ℤ))
    (show (0 : ℤ) < q by exact_mod_cast (by omega : 0 < q)) (by simpa using hpq)
  exact Int.natCast_inj.mp (by simpa only [Int.cast_natCast] using h)

/-- P0004 pages 5 and 6 section 1.4. Reduced fractions have unique numerators and denominators. -/
theorem center_injective {p q r s : ℕ} (hq : 1 ≤ q) (hs : 1 ≤ s)
    (hpq : p.Coprime q) (hrs : r.Coprime s)
    (he : (p : ℚ) / q = (r : ℚ) / s) : p = r ∧ q = s := by
  have hden : q = s := by rw [← center_den hq hpq, he, center_den hs hrs]
  subst s
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hnum : (p : ℚ) = r := (div_left_inj' hqQ).mp he
  exact ⟨by exact_mod_cast hnum, rfl⟩

/-- P0004 pages 5 and 6 section 1.4. A mediant lies strictly between its two distinct fractions. -/
theorem mediant_strict {r s : ℚ} (hrs : r < s) : r < mediant r s ∧ mediant r s < s := by
  obtain ⟨h1, h2⟩ := Decomp296Farey.mediant_gaps hrs
  have hr : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hs : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  have hp1 : (0 : ℝ) < 1 / ((r.den : ℝ) * (r.den + s.den : ℕ)) := by positivity
  have hp2 : (0 : ℝ) < 1 / ((s.den : ℝ) * (r.den + s.den : ℕ)) := by positivity
  constructor
  · exact_mod_cast (by linarith : (r : ℝ) < mediant r s)
  · exact_mod_cast (by linarith : (mediant r s : ℝ) < s)

/-- P0004 pages 5 and 6 section 1.4. Every reduced center belongs to the translated Farey set. -/
theorem center_mem {N p q : ℕ} (hq : 1 ≤ q) (hqN : q ≤ N)
    (hp : p < q) (hpq : p.Coprime q) : (p : ℚ) / q ∈ fareyPoints N := by
  have hqQ : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
  apply Decomp354h.farey_mem_of_den ((center_den hq hpq).le.trans hqN)
  · have : (0 : ℚ) ≤ p / q := by positivity
    linarith
  · have : (p : ℚ) / q ≤ 1 := (div_le_one hqQ).mpr (by exact_mod_cast hp.le)
    linarith

/-- P0004 pages 5 and 6 section 1.4. A selected successor is itself a Farey point. -/
theorem next_mem {N : ℕ} {r s : ℚ} (hs : s ∈ fareyPoints N) (hrs : r < s) :
    fareyNext N r ∈ fareyPoints N := by
  have h : ((fareyPoints N).filter fun t => r < t).Nonempty :=
    ⟨s, mem_filter.mpr ⟨hs, hrs⟩⟩
  unfold fareyNext
  rw [dif_pos h]
  exact (mem_filter.mp (min'_mem _ h)).1

/-- P0004 pages 5 and 6 section 1.4. A selected predecessor is itself a Farey point. -/
theorem prev_mem {N : ℕ} {r s : ℚ} (hr : r ∈ fareyPoints N) (hrs : r < s) :
    fareyPrev N s ∈ fareyPoints N := by
  have h : ((fareyPoints N).filter fun t => t < s).Nonempty :=
    ⟨r, mem_filter.mpr ⟨hr, hrs⟩⟩
  unfold fareyPrev
  rw [dif_pos h]
  exact (mem_filter.mp (max'_mem _ h)).1

/-- P0004 pages 5 and 6 section 1.4. The right mediant of an earlier center is no later than the left mediant of a later center. -/
theorem mediant_order {N : ℕ} (hN : 1 ≤ N) {r s : ℚ}
    (hr : r ∈ fareyPoints N) (hs : s ∈ fareyPoints N)
    (hr0 : 0 ≤ r) (hs1 : s ≤ 1) (hrs : r < s) :
    mediant r (fareyNext N r) ≤ mediant (fareyPrev N s) s := by
  have hr1 : r ≤ 1 := hrs.le.trans hs1
  have hs0 : 0 ≤ s := hr0.trans hrs.le
  obtain ⟨_, hrnext, _, _⟩ := Decomp296Farey.farey_neighbors hN hr0 hr1
  obtain ⟨hsprev, _, _, _⟩ := Decomp296Farey.farey_neighbors hN hs0 hs1
  have hnext : fareyNext N r ≤ s := Decomp354h.farey_next_min hs hrs
  have hprev : r ≤ fareyPrev N s := Decomp354h.farey_prev_max hr hrs
  rcases hnext.eq_or_lt with he | ht
  · have hprev_eq : fareyPrev N s = r := by
      apply le_antisymm _ hprev
      by_contra hh
      have hh' : r < fareyPrev N s := lt_of_not_ge hh
      have hmin := Decomp354h.farey_next_min (prev_mem hr hrs) hh'
      rw [he] at hmin
      exact (not_le_of_gt hsprev) hmin
    rw [he, hprev_eq]
  · have hmid := Decomp354h.farey_prev_max (next_mem hs hrs) ht
    exact (mediant_strict hrnext).2.le.trans (hmid.trans (mediant_strict hsprev).1.le)

#print axioms center_injective
#print axioms mediant_strict
#print axioms center_den
#print axioms center_mem
#print axioms next_mem
#print axioms prev_mem
#print axioms mediant_order
end LeanLab.HardyLittlewood1923.Geometry448

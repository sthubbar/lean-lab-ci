import LeanLab.HardyLittlewood1923.Decomp276a

/-!
AI wrote this Lean code for CODEX task296.
P0004 page 5 section 1.4 and page 25 equation 3.152.
These rational estimates supply lower bounds on mediant arc widths.
Binary Goldbach is OPEN.
-/

open Real

namespace LeanLab.HardyLittlewood1923.Decomp296Farey

open LeanLab.HardyLittlewood1923.Decomp276a

/-- P0004 page 25 after equation 3.152, the two distances from a mediant. -/
theorem mediant_gaps {r s : ℚ} (hrs : r < s) :
    1 / ((r.den : ℝ) * (r.den + s.den : ℕ)) ≤ (mediant r s : ℝ) - r ∧
    1 / ((s.den : ℝ) * (r.den + s.den : ℕ)) ≤ (s : ℝ) - mediant r s := by
  have hrQ : (0 : ℚ) < r.den := by exact_mod_cast r.pos
  have hsQ : (0 : ℚ) < s.den := by exact_mod_cast s.pos
  have hrR : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hsR : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  have hcQ : (r.num : ℚ) * s.den < (s.num : ℚ) * r.den := by
    rw [← r.num_div_den, ← s.num_div_den] at hrs
    exact (div_lt_div_iff₀ hrQ hsQ).mp hrs
  have hcZ : r.num * (s.den : ℤ) < s.num * (r.den : ℤ) := by exact_mod_cast hcQ
  have hc : (1 : ℝ) ≤ (s.num : ℝ) * r.den - (r.num : ℝ) * s.den := by
    exact_mod_cast (show (1 : ℤ) ≤ s.num * (r.den : ℤ) - r.num * (s.den : ℤ) by omega)
  have hrd : (r : ℝ) = (r.num : ℝ) / r.den := Rat.cast_def r
  have hsd : (s : ℝ) = (s.num : ℝ) / s.den := Rat.cast_def s
  have hmr : (mediant r s : ℝ) - r =
      ((s.num : ℝ) * r.den - (r.num : ℝ) * s.den) /
        ((r.den : ℝ) * (r.den + s.den : ℕ)) := by
    simp only [mediant, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, Int.cast_add]
    rw [hrd]
    push_cast
    field_simp
    ring
  have hms : (s : ℝ) - mediant r s =
      ((s.num : ℝ) * r.den - (r.num : ℝ) * s.den) /
        ((s.den : ℝ) * (r.den + s.den : ℕ)) := by
    simp only [mediant, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, Int.cast_add]
    rw [hsd]
    push_cast
    field_simp
    ring
  rw [hmr, hms]
  constructor <;> exact div_le_div_of_nonneg_right hc (by positivity)

#print axioms mediant_gaps

/-- P0004 page 5 section 1.4, every reduced point has denominator at most the Farey order. -/
theorem fareyPoints_den_le {N : ℕ} {r : ℚ} (hr : r ∈ fareyPoints N) : r.den ≤ N := by
  obtain ⟨q, hq, hr⟩ := Finset.mem_biUnion.mp hr
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
  have hqp : (0 : ℤ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
  have hc := (Finset.mem_filter.mp hp).2
  have hd := Rat.den_div_eq_of_coprime hqp (by simpa using hc)
  rw [show ((p : ℚ) / q).den = q by simpa using hd]
  exact (Finset.mem_Icc.mp hq).2

/-- P0004 page 5 section 1.4, translates give points to either side of the unit interval. -/
theorem fareyPoints_extremes {N : ℕ} (hN : 1 ≤ N) :
    (-1 : ℚ) ∈ fareyPoints N ∧ (2 : ℚ) ∈ fareyPoints N := by
  constructor
  · apply Finset.mem_biUnion.mpr
    refine ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨(-1 : ℤ), ?_, by norm_num⟩
    norm_num
  · apply Finset.mem_biUnion.mpr
    refine ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨(2 : ℤ), ?_, by norm_num⟩
    norm_num

/-- P0004 page 5 section 1.4, the selected neighbors are strict and have bounded denominators. -/
theorem farey_neighbors {N : ℕ} (hN : 1 ≤ N) {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    fareyPrev N r < r ∧ r < fareyNext N r ∧
      (fareyPrev N r).den ≤ N ∧ (fareyNext N r).den ≤ N := by
  have hp : ((fareyPoints N).filter fun t => t < r).Nonempty :=
    ⟨-1, Finset.mem_filter.mpr ⟨(fareyPoints_extremes hN).1, by linarith⟩⟩
  have hs : ((fareyPoints N).filter fun t => r < t).Nonempty :=
    ⟨2, Finset.mem_filter.mpr ⟨(fareyPoints_extremes hN).2, by linarith⟩⟩
  have hpm : fareyPrev N r ∈ (fareyPoints N).filter (fun t => t < r) := by
    simpa only [fareyPrev, dif_pos hp] using Finset.max'_mem _ hp
  have hsm : fareyNext N r ∈ (fareyPoints N).filter (fun t => r < t) := by
    simpa only [fareyNext, dif_pos hs] using Finset.min'_mem _ hs
  exact ⟨(Finset.mem_filter.mp hpm).2, (Finset.mem_filter.mp hsm).2,
    fareyPoints_den_le (Finset.mem_filter.mp hpm).1,
    fareyPoints_den_le (Finset.mem_filter.mp hsm).1⟩

#print axioms fareyPoints_den_le
#print axioms fareyPoints_extremes
#print axioms farey_neighbors

/-- P0004 page 25 after equation 3.152, the two actual angular width bounds. -/
theorem arc_widths {N p q : ℕ} (hN : 1 ≤ N) (hq : 1 ≤ q) (hqN : q ≤ N)
    (hp : p < q) (hpq : p.Coprime q) :
    1 / (2 * (q : ℝ) * N) ≤ -arcLeft N p q ∧
      1 / (2 * (q : ℝ) * N) ≤ arcRight N p q := by
  let r : ℚ := (p : ℚ) / q
  have hqQ : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    exact (div_le_one hqQ).mpr (by exact_mod_cast hp.le)
  have hrd : r.den = q := by
    have hd := Rat.den_div_eq_of_coprime (a := (p : ℤ))
      (show (0 : ℤ) < q by exact_mod_cast (by omega : 0 < q)) (by simpa using hpq)
    apply Int.natCast_inj.mp
    simpa only [r, Int.cast_natCast] using hd
  obtain ⟨hprev, hnext, hpden, hsden⟩ := farey_neighbors hN hr0 hr1
  have hgL := (mediant_gaps hprev).2
  have hgR := (mediant_gaps hnext).1
  rw [hrd] at hgL hgR
  have hb {d : ℕ} (hd : d ≤ N) :
      1 / (2 * (q : ℝ) * N) ≤ 1 / ((q : ℝ) * (d + q : ℕ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    have hdR : (d : ℝ) ≤ N := by exact_mod_cast hd
    have hqNR : (q : ℝ) ≤ N := by exact_mod_cast hqN
    push_cast
    nlinarith
  have hleft : 1 / (2 * (q : ℝ) * N) ≤
      (r : ℝ) - mediant (fareyPrev N r) r := (hb hpden).trans hgL
  have hright : 1 / (2 * (q : ℝ) * N) ≤
      (mediant r (fareyNext N r) : ℝ) - r := by
    exact (hb hsden).trans (by simpa only [Nat.add_comm] using hgR)
  have hfac : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
  have hleft0 : 0 ≤ (r : ℝ) - mediant (fareyPrev N r) r :=
    (by positivity : (0 : ℝ) ≤ 1 / (2 * (q : ℝ) * N)).trans hleft
  have hright0 : 0 ≤ (mediant r (fareyNext N r) : ℝ) - r :=
    (by positivity : (0 : ℝ) ≤ 1 / (2 * (q : ℝ) * N)).trans hright
  have heL : -arcLeft N p q = 2 * π * ((r : ℝ) - mediant (fareyPrev N r) r) := by
    change -(2 * π * ((mediant (fareyPrev N r) r - r : ℚ) : ℝ)) = _
    push_cast
    ring
  have heR : arcRight N p q = 2 * π * ((mediant r (fareyNext N r) : ℝ) - r) := by
    change 2 * π * ((mediant r (fareyNext N r) - r : ℚ) : ℝ) = _
    push_cast
    rfl
  rw [heL, heR]
  exact ⟨hleft.trans (le_mul_of_one_le_left hleft0 hfac),
    hright.trans (le_mul_of_one_le_left hright0 hfac)⟩

#print axioms arc_widths

end LeanLab.HardyLittlewood1923.Decomp296Farey

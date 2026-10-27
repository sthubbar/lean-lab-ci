import LeanLab.LiuWang2002.Vaughan109
import LeanLab.LiuWang2002.ArcBounds109

/-! The named circle method objects of P0023, pages 144 and 145.
AI wrote the Lean code. Binary Goldbach is open. -/

namespace LeanLab.LiuWang2002.Arcs109
open Real Set MeasureTheory Vaughan109

/-- Denominator cutoff in display 3.1, page 144. -/
noncomputable def Q (N : ℝ) : ℝ := N / log N ^ 7

/-- Short arc radius in display 3.3, page 144. -/
noncomputable def delta (N : ℝ) (q : ℕ) : ℝ := 3.36 * log N ^ 3 / (10 * Real.pi * q * N)

/-- Rational approximation arc in the paragraph after display 3.2, page 144. -/
noncomputable def rationalArc (N : ℝ) (a q : ℕ) : Set ℝ :=
  Icc ((a : ℝ) / q - 1 / ((q : ℝ) * Q N)) ((a : ℝ) / q + 1 / ((q : ℝ) * Q N))

/-- The integration interval in Section 3, page 144. -/
noncomputable def domain (N : ℝ) : Set ℝ := Icc (1 / Q N) (1 + 1 / Q N)

/-- The major arcs M1 in display 3.4, page 144. -/
noncomputable def major1 (N : ℝ) : Set ℝ :=
  ⋃ q : ℕ, ⋃ a : ℕ,
    if 1 ≤ q ∧ (q : ℝ) ≤ log N ^ 3 ∧ 1 ≤ a ∧ a ≤ q ∧ a.Coprime q then
      Icc ((a : ℝ) / q - delta N q) ((a : ℝ) / q + delta N q) else ∅

/-- The union preceding subtraction of M1 in display 3.5, page 144. -/
noncomputable def fareySmall (N : ℝ) : Set ℝ :=
  ⋃ q : ℕ, ⋃ a : ℕ,
    if 1 ≤ q ∧ (q : ℝ) ≤ log N ^ 3 ∧ 1 ≤ a ∧ a ≤ q ∧ a.Coprime q then
      rationalArc N a q else ∅

/-- The arcs M2 in display 3.5, page 144. -/
noncomputable def major2 (N : ℝ) : Set ℝ := fareySmall N \ major1 N

/-- The arcs M3 in display 3.6, page 144. -/
noncomputable def major3 (N : ℝ) : Set ℝ :=
  ⋃ q : ℕ, ⋃ a : ℕ,
    if log N ^ 3 < (q : ℝ) ∧ (q : ℝ) ≤ log N ^ 6 ∧ 1 ≤ a ∧ a ≤ q ∧ a.Coprime q then
      rationalArc N a q else ∅

/-- The arcs M4 in display 3.7, page 144. -/
noncomputable def minor4 (N : ℝ) : Set ℝ := domain N \ (major1 N ∪ major2 N ∪ major3 N)

/-- The integrand of display 3.11, page 145, with the cutoff of display 3.8. -/
noncomputable def kernel (N α : ℝ) : ℂ :=
  (S N 0.001 α) ^ 3 * Complex.exp (-2 * Real.pi * Complex.I * (N * α))

/-- First arc integral of display 3.11, page 145. -/
noncomputable def I1 (N : ℝ) : ℂ := ∫ α in major1 N, kernel N α
/-- Second arc integral of display 3.11, page 145. -/
noncomputable def I2 (N : ℝ) : ℂ := ∫ α in major2 N, kernel N α
/-- Third arc integral of display 3.11, page 145. -/
noncomputable def I3 (N : ℝ) : ℂ := ∫ α in major3 N, kernel N α
/-- Fourth arc integral of display 3.11, page 145. -/
noncomputable def I4 (N : ℝ) : ℂ := ∫ α in minor4 N, kernel N α

/-- The major and minor arc sets in display 3.11 are measurable. -/
theorem arcs_measurable (N : ℝ) :
    MeasurableSet (major1 N) ∧ MeasurableSet (major2 N) ∧
      MeasurableSet (major3 N) ∧ MeasurableSet (minor4 N) := by
  have h1 : MeasurableSet (major1 N) := by unfold major1; measurability
  have hf : MeasurableSet (fareySmall N) := by unfold fareySmall rationalArc; measurability
  have h2 : MeasurableSet (major2 N) := hf.diff h1
  have h3 : MeasurableSet (major3 N) := by unfold major3 rationalArc; measurability
  exact ⟨h1, h2, h3, measurableSet_Icc.diff ((h1.union h2).union h3)⟩

/-- The finite exponential sum in display 3.8 is continuous in alpha. -/
theorem continuous_S (N c : ℝ) : Continuous (S N c) := by
  unfold S weightedSum
  apply continuous_finset_sum
  intro n hn
  split_ifs <;> fun_prop

/-- The circle method integrand in display 3.11 is continuous. -/
theorem continuous_kernel (N : ℝ) : Continuous (kernel N) := by
  unfold kernel
  have hs := continuous_S N 0.001
  fun_prop

/-- M1 and M2 are disjoint by display 3.5, page 144. -/
theorem major1_disjoint_major2 (N : ℝ) : Disjoint (major1 N) (major2 N) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  exact hx2.2 hx1

/-- The four arcs cover the integration interval after clipping, displays 3.4 to 3.7. -/
theorem domain_partition (N : ℝ) :
    (domain N ∩ major1 N) ∪ (domain N ∩ major2 N) ∪
      (domain N ∩ major3 N) ∪ minor4 N = domain N := by
  unfold minor4
  ext x
  simp only [mem_union, mem_inter_iff, mem_diff]
  tauto

/-- Continuity makes the full circle integral well defined, display 3.10, page 145. -/
theorem kernel_integrable_domain (N : ℝ) : IntegrableOn (kernel N) (domain N) :=
  (continuous_kernel N).continuousOn.integrableOn_compact isCompact_Icc

/-- Every rational arc with q plus one at most Q lies in domain, page 144. -/
theorem rationalArc_subset_domain (N : ℝ) (a q : ℕ) (ha : 1 ≤ a) (haq : a ≤ q)
    (hQ : (q : ℝ) + 1 ≤ Q N) : rationalArc N a q ⊆ domain N := by
  have haqR : (a : ℝ) ≤ q := by exact_mod_cast haq
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hq : 0 < (q : ℝ) := by linarith
  have hQ0 : 0 < Q N := by linarith
  intro x hx
  rcases hx with ⟨hxl, hxu⟩
  constructor
  · apply le_trans ?_ hxl
    have he : (a : ℝ) / q - 1 / ((q : ℝ) * Q N) = ((a : ℝ) * Q N - 1) / ((q : ℝ) * Q N) := by
      field_simp
    rw [he, le_div_iff₀ (mul_pos hq hQ0)]
    have he' : 1 / Q N * ((q : ℝ) * Q N) = q := by field_simp
    rw [he']
    nlinarith [mul_nonneg (show 0 ≤ (a : ℝ) - 1 by linarith) hQ0.le]
  · apply le_trans hxu
    have hcenter : (a : ℝ) / q ≤ 1 := (div_le_one hq).mpr haqR
    have hr : 1 / ((q : ℝ) * Q N) ≤ 1 / Q N := by
      apply one_div_le_one_div_of_le hQ0
      have hq1 : (1 : ℝ) ≤ q := by linarith
      nlinarith
    linarith

/-- The short radius is below the rational approximation radius, page 144 after 3.3. -/
theorem delta_le_radius (N : ℝ) (q : ℕ) (hN : exp 3100 ≤ N) (hq : 1 ≤ q) :
    delta N q ≤ 1 / ((q : ℝ) * Q N) := by
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hLp : 0 < log N := by
    have := (le_log_iff_exp_le hNp).mpr hN
    linarith
  have hL1 : 1 ≤ log N := by
    have := (le_log_iff_exp_le hNp).mpr hN
    linarith
  have hqr : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hc : (3.36 : ℝ) / (10 * Real.pi) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have hp : log N ^ 3 ≤ log N ^ 7 := by
    have hh := rpow_le_rpow_of_exponent_le hL1 (show (3 : ℝ) ≤ 7 by norm_num)
    simpa using hh
  have hr : 1 / ((q : ℝ) * Q N) = log N ^ 7 / ((q : ℝ) * N) := by
    unfold Q
    field_simp
  calc
    delta N q = (3.36 / (10 * Real.pi)) * (log N ^ 3 / ((q : ℝ) * N)) := by
      unfold delta
      field_simp
    _ ≤ log N ^ 3 / ((q : ℝ) * N) := mul_le_of_le_one_left (by positivity) hc
    _ ≤ log N ^ 7 / ((q : ℝ) * N) := div_le_div_of_nonneg_right hp (by positivity)
    _ = _ := hr.symm

/-- The first major arcs lie in the full rational arcs, displays 3.3 and 3.4. -/
theorem major1_subset_fareySmall (N : ℝ) (hN : exp 3100 ≤ N) :
    major1 N ⊆ fareySmall N := by
  intro x hx
  simp only [major1, mem_iUnion] at hx
  obtain ⟨q, a, hx⟩ := hx
  split_ifs at hx with h
  · unfold fareySmall
    refine mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨a, ?_⟩⟩
    rw [if_pos h]
    have hr := delta_le_radius N q hN h.1
    exact ⟨(by linarith [hx.1]), (by linarith [hx.2])⟩
  · exact False.elim (notMem_empty x hx)

/-- The denominator cutoff leaves room for every rational arc, page 144. -/
theorem cutoff_le_Q (N : ℝ) (hN : exp 3100 ≤ N) : log N ^ 6 + 1 ≤ Q N := by
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hL : 3100 ≤ log N := (le_log_iff_exp_le hNp).mpr hN
  have hs := ArcBounds109.denominator_separation (log N) hL
  rw [exp_log hNp] at hs
  have hp : (1 : ℝ) ≤ log N ^ 6 := one_le_pow₀ (by linarith : 1 ≤ log N)
  unfold Q
  linarith

/-- The full arcs with q at most P lie inside domain, page 144. -/
theorem fareySmall_subset_domain (N : ℝ) (hN : exp 3100 ≤ N) :
    fareySmall N ⊆ domain N := by
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hL : 3100 ≤ log N := (le_log_iff_exp_le hNp).mpr hN
  have hp : log N ^ 3 ≤ log N ^ 6 := by
    have hh := rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ log N)
      (show (3 : ℝ) ≤ 6 by norm_num)
    simpa using hh
  have hQ := cutoff_le_Q N hN
  intro x hx
  simp only [fareySmall, mem_iUnion] at hx
  obtain ⟨q, a, hx⟩ := hx
  split_ifs at hx with h
  · exact rationalArc_subset_domain N a q h.2.2.1 h.2.2.2.1
      (by linarith [h.2.1]) hx
  · exact False.elim (notMem_empty x hx)

/-- The arcs with P below q at most P1 lie inside domain, page 144. -/
theorem major3_subset_domain (N : ℝ) (hN : exp 3100 ≤ N) :
    major3 N ⊆ domain N := by
  have hQ := cutoff_le_Q N hN
  intro x hx
  simp only [major3, mem_iUnion] at hx
  obtain ⟨q, a, hx⟩ := hx
  split_ifs at hx with h
  · exact rationalArc_subset_domain N a q h.2.2.1 h.2.2.2.1
      (by linarith [h.2.1]) hx
  · exact False.elim (notMem_empty x hx)

/-- The actual four arc integrands are integrable in the paper's N range, page 145. -/
theorem arc_integrable (N : ℝ) (hN : exp 3100 ≤ N) :
    IntegrableOn (kernel N) (major1 N) ∧ IntegrableOn (kernel N) (major2 N) ∧
      IntegrableOn (kernel N) (major3 N) ∧ IntegrableOn (kernel N) (minor4 N) := by
  have hd := kernel_integrable_domain N
  have hf := fareySmall_subset_domain N hN
  exact ⟨hd.mono_set ((major1_subset_fareySmall N hN).trans hf),
    hd.mono_set (fun x hx => hf hx.1), hd.mono_set (major3_subset_domain N hN),
    hd.mono_set (fun x hx => hx.1)⟩

/-- Distinct rational centers have spacing at least one divided by q r, page 144. -/
theorem rational_spacing (a q b r : ℕ) (hq : 0 < q) (hr : 0 < r) (hne : a * r ≠ b * q) :
    1 / ((q : ℝ) * r) ≤ |(a : ℝ) / q - (b : ℝ) / r| := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hi : (a : ℤ) * r - (b : ℤ) * q ≠ 0 := by
    intro h
    apply hne
    have hh := sub_eq_zero.mp h
    exact_mod_cast hh
  have habs : (1 : ℝ) ≤ |(a : ℝ) * r - (b : ℝ) * q| := by
    exact_mod_cast Int.one_le_abs hi
  rw [div_sub_div _ _ hqR.ne' hrR.ne', abs_div, abs_of_pos (mul_pos hqR hrR)]
  exact div_le_div_of_nonneg_right (by simpa [mul_comm] using habs) (mul_pos hqR hrR).le

/-- Rational arcs with separated centers are disjoint, page 144 before display 3.3. -/
theorem rationalArc_disjoint (N : ℝ) (a q b r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hne : a * r ≠ b * q) (hQ : (q : ℝ) + r < Q N) :
    Disjoint (rationalArc N a q) (rationalArc N b r) := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hQR : 0 < Q N := by linarith
  have hgap := rational_spacing a q b r hq hr hne
  have hrad : 1 / ((q : ℝ) * Q N) + 1 / ((r : ℝ) * Q N) < 1 / ((q : ℝ) * r) := by
    have he : 1 / ((q : ℝ) * Q N) + 1 / ((r : ℝ) * Q N) =
        ((q : ℝ) + r) / ((q : ℝ) * r * Q N) := by field_simp; ring
    rw [he, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (mul_pos hqR hrR) (sub_pos.mpr hQ)]
  rw [Set.disjoint_left]
  intro x hx hy
  have hdist : |(a : ℝ) / q - (b : ℝ) / r| ≤
      1 / ((q : ℝ) * Q N) + 1 / ((r : ℝ) * Q N) := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  exact (not_lt_of_ge (hgap.trans hdist)) hrad

/-- Reduced equal fractions have equal denominators, used on page 144. -/
theorem denominator_eq_of_cross_eq (a q b r : ℕ) (ha : a.Coprime q) (hb : b.Coprime r)
    (hcross : a * r = b * q) : q = r := by
  apply Nat.dvd_antisymm
  · apply ha.symm.dvd_of_dvd_mul_left
    rw [hcross]
    exact Nat.dvd_mul_left q b
  · apply hb.symm.dvd_of_dvd_mul_left
    rw [← hcross]
    exact Nat.dvd_mul_left r a

/-- The arcs with q at most P are disjoint from M3, page 144. -/
theorem fareySmall_disjoint_major3 (N : ℝ) (hN : exp 3100 ≤ N) :
    Disjoint (fareySmall N) (major3 N) := by
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hL : 3100 ≤ log N := (le_log_iff_exp_le hNp).mpr hN
  have hsep := ArcBounds109.denominator_separation (log N) hL
  rw [exp_log hNp] at hsep
  have hp : log N ^ 3 ≤ log N ^ 6 := by
    have hh := rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ log N)
      (show (3 : ℝ) ≤ 6 by norm_num)
    simpa using hh
  rw [Set.disjoint_left]
  intro x hx hy
  simp only [fareySmall, mem_iUnion] at hx
  simp only [major3, mem_iUnion] at hy
  obtain ⟨q, a, hx⟩ := hx
  obtain ⟨r, b, hy⟩ := hy
  split_ifs at hx with hq
  · split_ifs at hy with hr
    · have hqr : q ≠ r := by
        intro he
        have heR : (q : ℝ) = r := by exact_mod_cast he
        linarith [hq.2.1, hr.1]
      have hcross : a * r ≠ b * q := by
        intro he
        exact hqr (denominator_eq_of_cross_eq a q b r hq.2.2.2.2 hr.2.2.2.2 he)
      have hq0 : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq.1
      have hr0 : 0 < r := by omega
      have hQ : (q : ℝ) + r < Q N := by
        unfold Q
        linarith [hq.2.1, hr.2.1]
      exact (Set.disjoint_left.mp (rationalArc_disjoint N a q b r hq0 hr0 hcross hQ)) hx hy
    · exact False.elim (notMem_empty x hy)
  · exact False.elim (notMem_empty x hx)

/-- The actual four arcs partition the integration interval, displays 3.4 to 3.7. -/
theorem arcs_partition (N : ℝ) (hN : exp 3100 ≤ N) :
    major1 N ∪ major2 N ∪ major3 N ∪ minor4 N = domain N := by
  have hf := fareySmall_subset_domain N hN
  have h1 : major1 N ⊆ domain N := (major1_subset_fareySmall N hN).trans hf
  have h2 : major2 N ⊆ domain N := fun x hx => hf hx.1
  have hp := domain_partition N
  rw [inter_eq_right.mpr h1, inter_eq_right.mpr h2,
    inter_eq_right.mpr (major3_subset_domain N hN)] at hp
  exact hp

/-- Exact splitting into the four actual integrals, display 3.11 on page 145. -/
theorem integral_split (N : ℝ) (hN : exp 3100 ≤ N) :
    (∫ α in domain N, kernel N α) = I1 N + I2 N + I3 N + I4 N := by
  obtain ⟨hm1, hm2, hm3, hm4⟩ := arcs_measurable N
  obtain ⟨hi1, hi2, hi3, hi4⟩ := arc_integrable N hN
  have h13 : Disjoint (major1 N) (major3 N) :=
    (fareySmall_disjoint_major3 N hN).mono_left (major1_subset_fareySmall N hN)
  have h23 : Disjoint (major2 N) (major3 N) :=
    (fareySmall_disjoint_major3 N hN).mono_left (fun x hx => hx.1)
  have h123 : Disjoint (major1 N ∪ major2 N) (major3 N) := by
    rw [Set.disjoint_union_left]
    exact ⟨h13, h23⟩
  have h1234 : Disjoint (major1 N ∪ major2 N ∪ major3 N) (minor4 N) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact hy.2 hx
  have hi12 : IntegrableOn (kernel N) (major1 N ∪ major2 N) := hi1.union hi2
  have hi123 : IntegrableOn (kernel N) (major1 N ∪ major2 N ∪ major3 N) := hi12.union hi3
  rw [← arcs_partition N hN, setIntegral_union h1234 hm4 hi123 hi4,
    setIntegral_union h123 hm3 hi12 hi3,
    setIntegral_union (major1_disjoint_major2 N) hm2 hi1 hi2]
  rfl

end LeanLab.LiuWang2002.Arcs109

#print axioms LeanLab.LiuWang2002.Arcs109.arcs_measurable
#print axioms LeanLab.LiuWang2002.Arcs109.continuous_S
#print axioms LeanLab.LiuWang2002.Arcs109.continuous_kernel
#print axioms LeanLab.LiuWang2002.Arcs109.major1_disjoint_major2
#print axioms LeanLab.LiuWang2002.Arcs109.domain_partition

#print axioms LeanLab.LiuWang2002.Arcs109.kernel_integrable_domain
#print axioms LeanLab.LiuWang2002.Arcs109.rationalArc_subset_domain

#print axioms LeanLab.LiuWang2002.Arcs109.delta_le_radius
#print axioms LeanLab.LiuWang2002.Arcs109.major1_subset_fareySmall

#print axioms LeanLab.LiuWang2002.Arcs109.cutoff_le_Q
#print axioms LeanLab.LiuWang2002.Arcs109.fareySmall_subset_domain
#print axioms LeanLab.LiuWang2002.Arcs109.major3_subset_domain
#print axioms LeanLab.LiuWang2002.Arcs109.arc_integrable

#print axioms LeanLab.LiuWang2002.Arcs109.rational_spacing
#print axioms LeanLab.LiuWang2002.Arcs109.rationalArc_disjoint

#print axioms LeanLab.LiuWang2002.Arcs109.denominator_eq_of_cross_eq
#print axioms LeanLab.LiuWang2002.Arcs109.fareySmall_disjoint_major3

#print axioms LeanLab.LiuWang2002.Arcs109.arcs_partition
#print axioms LeanLab.LiuWang2002.Arcs109.integral_split

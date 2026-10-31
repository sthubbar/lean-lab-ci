import LeanLab.ChenDoubleSieve.FunctionalStatements
import LeanLab.ChenDoubleSieve.SigmaIntegral

/-!
# The global Buchstab bound quoted by Wu 2004

Source: https://arxiv.org/pdf/0705.1652, page 9, Lemma 2.10.
The bound is proved for every continuous function satisfying the defining delay equation.
Existence of that function is not asserted here.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Wu04Buchstab
open Wu04Functional (IsBuchstab)

/-- Wu's printed upper bound for u at least two. -/
def C : ℝ := 567144 / 1000000

/-- A finite logarithm enclosure certifies the tangent needed for the bound. -/
theorem log_recip_C : log (1 / C) ≤ C := by
  have hb := (Wu04Integral.log_bounds 8 (y := 1 / C) (by norm_num [C])).2
  apply hb.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, C, Finset.sum_range_succ]

/-- The tangent inequality works for every positive argument. -/
theorem one_add_log_le {y : ℝ} (hy : 0 < y) : 1 + log y ≤ C * (y + 1) := by
  have hc : 0 < C := by norm_num [C]
  have hlog := log_le_sub_one_of_pos (mul_pos hy hc)
  rw [log_mul hy.ne' hc.ne'] at hlog
  have hrec := log_recip_C
  rw [one_div, log_inv] at hrec
  nlinarith

/-- The delay equation determines omega explicitly between two and three. -/
theorem formula_two_three {ω : ℝ → ℝ} (hω : IsBuchstab ω) {u : ℝ} (hu : u ∈ Icc 2 3) :
    ω u = (1 + log (u - 1)) / u := by
  have hcont : ContinuousOn (fun t : ℝ => t * ω t) (Icc 2 u) :=
    continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
  have hder : ∀ t ∈ Ioo (2 : ℝ) u,
      HasDerivAt (fun v => v * ω v) ((t - 1)⁻¹) t := by
    intro t ht
    have he := hω.2.1 (t - 1) (by linarith [ht.1]) (by linarith [ht.2, hu.2])
    simpa only [he, one_div] using hω.2.2 t ht.1
  have hci : ContinuousOn (fun t : ℝ => (t - 1)⁻¹) (uIcc 2 u) := by
    rw [uIcc_of_le hu.1]
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht; linarith [ht.1]
  have hFTC := integral_eq_sub_of_hasDerivAt_of_le hu.1 hcont hder hci.intervalIntegrable
  have hI : (∫ t in (2 : ℝ)..u, (t - 1)⁻¹) = log (u - 1) := by
    rw [integral_comp_sub_right (fun t : ℝ => t⁻¹), integral_inv_of_pos (by norm_num) (by linarith [hu.1])]
    norm_num
  rw [hI, hω.2.1 2 (by norm_num) (by norm_num)] at hFTC
  apply (eq_div_iff (by linarith [hu.1] : u ≠ 0)).mpr
  norm_num at hFTC
  nlinarith

/-- The sharp tangent proves the initial interval bound. -/
theorem bound_two_three {ω : ℝ → ℝ} (hω : IsBuchstab ω) {u : ℝ} (hu : u ∈ Icc 2 3) :
    ω u ≤ C := by
  rw [formula_two_three hω hu, div_le_iff₀ (by linarith [hu.1])]
  have ht := one_add_log_le (y := u - 1) (by linarith [hu.1])
  nlinarith

/-- A constant upper bound propagates along the Buchstab delay equation. -/
theorem propagate_upper {ω : ℝ → ℝ} (hω : IsBuchstab ω) {c : ℝ}
    (hbase : ∀ u ∈ Icc (2 : ℝ) 3, ω u ≤ c) : ∀ u : ℝ, 2 ≤ u → ω u ≤ c := by
  have step : ∀ n : ℕ, ∀ u : ℝ, 2 ≤ u → u ≤ (n : ℝ) + 3 → ω u ≤ c := by
    intro n
    induction n with
    | zero =>
      intro u hu2 hu3
      exact hbase u ⟨hu2, by simpa using hu3⟩
    | succ n ih =>
      intro u hu2 huMax
      by_cases hsmall : u ≤ (n : ℝ) + 3
      · exact ih u hu2 hsmall
      let b : ℝ := n + 3
      have hb3 : 3 ≤ b := by dsimp [b]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hbu : b ≤ u := (lt_of_not_ge hsmall).le
      have hwb : ω b ≤ c := ih b (by linarith) le_rfl
      have hcont : ContinuousOn (fun t : ℝ => t * ω t) (Icc b u) :=
        continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
      have hci : ContinuousOn (fun t : ℝ => ω (t - 1)) (uIcc b u) := by
        rw [uIcc_of_le hbu]
        apply hω.1.comp (by fun_prop)
        intro t ht
        change 1 ≤ t - 1
        linarith [ht.1]
      have hFTC := integral_eq_sub_of_hasDerivAt_of_le hbu hcont
        (fun t ht => hω.2.2 t (by linarith [ht.1])) hci.intervalIntegrable
      have hI : (∫ t in b..u, ω (t - 1)) ≤ (u - b) * c := by
        have hm := integral_mono_on (μ := volume) hbu hci.intervalIntegrable intervalIntegrable_const
          (fun t ht => ih (t - 1) (by linarith [ht.1]) (by
            dsimp [b] at hbu
            push_cast at huMax
            linarith [ht.2]))
        simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm
      have hleft : b * ω b ≤ b * c := mul_le_mul_of_nonneg_left hwb (by linarith)
      have hmul : u * ω u ≤ u * c := by linarith
      by_contra hnot
      have hpos := mul_pos (show 0 < u by linarith) (sub_pos.mpr (lt_of_not_ge hnot))
      nlinarith
  intro u hu
  exact step ⌈u⌉₊ u hu (by linarith [Nat.le_ceil u])

/-- The quoted constant follows from the defining equations, with no cited numerical estimate. -/
theorem buchstab_le_567144 {ω : ℝ → ℝ} (hω : IsBuchstab ω) {u : ℝ} (hu : 2 ≤ u) :
    ω u ≤ (567144 / 1000000 : ℝ) :=
  propagate_upper hω (fun u hu => bound_two_three hω hu) u hu

end LeanLab.ChenDoubleSieve.Wu04Buchstab

#print axioms LeanLab.ChenDoubleSieve.Wu04Buchstab.log_recip_C
#print axioms LeanLab.ChenDoubleSieve.Wu04Buchstab.one_add_log_le
#print axioms LeanLab.ChenDoubleSieve.Wu04Buchstab.formula_two_three
#print axioms LeanLab.ChenDoubleSieve.Wu04Buchstab.bound_two_three
#print axioms LeanLab.ChenDoubleSieve.Wu04Buchstab.propagate_upper
#print axioms LeanLab.ChenDoubleSieve.Wu04Buchstab.buchstab_le_567144

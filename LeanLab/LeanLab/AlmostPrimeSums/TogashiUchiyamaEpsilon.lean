/-
AI-written Lean code, OpenAI Codex, task33, 2026-10-23, T1.
P0072 Togashi and Uchiyama 1964, pp. 65 to 67.
Continuity of I at zero and the positive epsilon choice in Section 5.
The sieve estimates remain cited inputs. Goldbach is open.
-/
import LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex

open Real Set Filter MeasureTheory

noncomputable section
namespace LeanLab.AlmostPrimeSums.TogashiUchiyamaEpsilon

open TogashiUchiyama TogashiUchiyamaConvex

/-- The parameter range for the last step of Section 5. -/
def E : Set ℝ := Icc 0 (1 / 30)

def A (ε u : ℝ) : ℝ := 3 * (1 - 2 * ε - 1 / u)

def K : ℝ := 144 * exp (2 * eulerMascheroniConstant)

def I (ε : ℝ) : ℝ := ∫ u in (3 : ℝ)..6, Ceps ε u / u

lemma A_range {ε u : ℝ} (hε : ε ∈ E) (hu : u ∈ Icc (3 : ℝ) 6) :
    1 < A ε u ∧ A ε u ≤ 3 := by
  have hu0 : 0 < u := by linarith [hu.1]
  have h1 : 1 / u ≤ (1 / 3 : ℝ) := one_div_le_one_div_of_le (by norm_num) hu.1
  have h0 : 0 < 1 / u := by positivity
  rcases hε with ⟨hε0, hε1⟩
  dsimp [A]
  constructor <;> linarith

lemma q_ge_one {a : ℝ} (ha : a ∈ Icc (1 : ℝ) 3) : 1 ≤ q a := by
  have h := q_strictMonoOn.monotoneOn ⟨le_rfl, by norm_num⟩ ha ha.1
  norm_num [q] at h
  exact h

lemma Ceps_eq {ε u : ℝ} (hε : ε ∈ E) (hu : u ∈ Icc (3 : ℝ) 6) :
    Ceps ε u / u = K / q (A ε u) / u := by
  have ha := A_range hε hu
  change 1 < 3 * (1 - 2 * ε - 1 / u) ∧ _ at ha
  simp only [Ceps, D, A, K]
  rw [ite_eq_right (by linarith [ha.1] : ¬ 3 * (1 - 2 * ε - 1 / u) ≤ 1)]

lemma integrand_continuousOn {ε : ℝ} (hε : ε ∈ E) :
    ContinuousOn (fun u => Ceps ε u / u) (Icc (3 : ℝ) 6) := by
  have hA : ContinuousOn (A ε) (Icc (3 : ℝ) 6) := by
    unfold A
    fun_prop (disch := intro u hu; linarith [hu.1])
  have hqbase : ContinuousOn q (Icc (1 : ℝ) 3) :=
    fun a ha => (hasDerivAt_q (by linarith [ha.1])).continuousAt.continuousWithinAt
  have hq : ContinuousOn (fun u => q (A ε u)) (Icc (3 : ℝ) 6) :=
    hqbase.comp hA (fun u hu => ⟨(A_range hε hu).1.le, (A_range hε hu).2⟩)
  have hc : ContinuousOn (fun u => K / q (A ε u) / u) (Icc (3 : ℝ) 6) := by
    apply ContinuousOn.div (ContinuousOn.div continuousOn_const hq ?_) continuousOn_id ?_
    · intro u hu
      exact (q_pos (A_range hε hu).1.le (A_range hε hu).2).ne'
    · intro u hu
      change u ≠ 0
      linarith [hu.1]
  exact hc.congr (fun u hu => Ceps_eq hε hu)

lemma integrand_le {ε u : ℝ} (hε : ε ∈ E) (hu : u ∈ Icc (3 : ℝ) 6) :
    ‖Ceps ε u / u‖ ≤ K := by
  have ha := A_range hε hu
  have hq := q_ge_one ⟨ha.1.le, ha.2⟩
  have hu0 : 0 < u := by linarith [hu.1]
  have hq0 : 0 < q (A ε u) := lt_of_lt_of_le zero_lt_one hq
  have hK : 0 ≤ K := by unfold K; positivity
  rw [Ceps_eq hε hu, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    K / q (A ε u) / u ≤ K / q (A ε u) := div_le_self (by positivity) (by linarith [hu.1])
    _ ≤ K := div_le_self hK hq

lemma integrand_continuousWithinAt (u : ℝ) (hu : u ∈ Icc (3 : ℝ) 6) :
    ContinuousWithinAt (fun ε => Ceps ε u / u) E 0 := by
  have ha0 := A_range (show (0 : ℝ) ∈ E by norm_num [E]) hu
  have hA : ContinuousAt (fun ε => A ε u) 0 := by unfold A; fun_prop
  have hq : ContinuousAt (fun ε => q (A ε u)) 0 :=
    (hasDerivAt_q (by linarith [ha0.1])).continuousAt.comp hA
  have hc : ContinuousWithinAt (fun ε => K / q (A ε u) / u) E 0 :=
    ((continuousAt_const.div hq (q_pos ha0.1.le ha0.2).ne').div_const u).continuousWithinAt
  apply hc.congr
  · intro ε hε
    exact Ceps_eq hε hu
  · exact Ceps_eq (ε := 0) (by norm_num [E]) hu

lemma I_continuousWithinAt_zero : ContinuousWithinAt I E 0 := by
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => K)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [uIoc_of_le (by norm_num : (3 : ℝ) ≤ 6)]
    exact ((integrand_continuousOn hε).aestronglyMeasurable measurableSet_Icc).mono_set Ioc_subset_Icc_self
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ae_of_all _ (fun u hu => integrand_le hε (by
      rw [uIoc_of_le (by norm_num : (3 : ℝ) ≤ 6)] at hu
      exact ⟨hu.1.le, hu.2⟩))
  · exact intervalIntegrable_const
  · exact ae_of_all _ (fun u hu => integrand_continuousWithinAt u (by
      rw [uIoc_of_le (by norm_num : (3 : ℝ) ≤ 6)] at hu
      exact ⟨hu.1.le, hu.2⟩))

lemma I_zero_lt : I 0 < 79.3025 := by
  have heq : I 0 = ∫ u in (3 : ℝ)..6, C0 u / u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (3 : ℝ) ≤ 6)] at hu
    change Ceps 0 u / u = C0 u / u
    rw [Ceps_eq (ε := 0) (by norm_num [E]) hu]
    simp only [K, A, C0, sub, mul_zero, sub_zero]
  rw [heq]
  exact I0_u_lt

/-- A positive interval of epsilon values satisfies the required integral bound. -/
theorem exists_epsilon_interval : ∃ η : ℝ, 0 < η ∧ η < 1 / 30 ∧
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ η → I ε < 79.3026 := by
  have hgap : 0 < (79.3026 : ℝ) - I 0 := by linarith [I_zero_lt]
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousWithinAt_iff.mp I_continuousWithinAt_zero _ hgap
  let η : ℝ := min (δ / 2) (1 / 60)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hη30 : η < 1 / 30 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨η, hη, hη30, ?_⟩
  intro ε hε0 hεη
  have hεE : ε ∈ E := ⟨hε0, hεη.trans hη30.le⟩
  have hd : dist ε 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hε0]
    have h : η ≤ δ / 2 := min_le_left _ _
    linarith
  have hv := hb hεE hd
  rw [Real.dist_eq] at hv
  have h := (abs_lt.mp hv).2
  linarith

theorem exists_epsilon : ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 30 ∧ I ε < 79.3026 := by
  obtain ⟨η, hη, hη30, hI⟩ := exists_epsilon_interval
  exact ⟨η, hη, hη30, hI η hη.le le_rfl⟩

end LeanLab.AlmostPrimeSums.TogashiUchiyamaEpsilon

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaEpsilon.A_range

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaEpsilon.q_ge_one

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaEpsilon.Ceps_eq

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaEpsilon.integrand_continuousOn

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaEpsilon.integrand_le

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaEpsilon.integrand_continuousWithinAt

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaEpsilon.I_continuousWithinAt_zero

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaEpsilon.I_zero_lt

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaEpsilon.exists_epsilon_interval

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaEpsilon.exists_epsilon

/-
P0070. A. Perelli and J. Pintz, On the exceptional set for the 2k-twin primes problem,
Compositio Math. 82, 1992, pp. 355 to 372, Section 5, p. 364.

ROUTE BURST session 9, 2026-11-12. The measure theory for `clip_average_proved`: the
integrability of the moving sums, the exchange of the integrals over `x` and over the window
`u`, and the two end blocks. All PROVED.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.Burst9Clip

namespace LeanLab.PerelliPintz1992.Burst9
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992 LeanLab.PerelliPintz1992.Decomp97 LeanLab.PerelliPintz1992.Decomp1624
open LeanLab.PerelliPintz1992.Burst8P2

noncomputable section

variable {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))

/-- `|S(x, u)|²`. -/
def Fm (x u : ℝ) : ℝ := ‖movingSum χ x u‖ ^ 2

theorem Fm_nonneg (x u : ℝ) : 0 ≤ Fm χ x u := sq_nonneg _

theorem Fm_measurable : Measurable (fun p : ℝ × ℝ => Fm χ p.1 p.2) :=
  (movingSum_measurable χ).norm.pow_const 2

/-- The bound for `x + u ≤ R`. -/
def SR (R : ℝ) : ℝ := ∑ n ∈ Finset.range (⌊R⌋₊ + 1), ‖cf χ n‖

theorem Fm_le {R x u : ℝ} (h : x + u ≤ R) : Fm χ x u ≤ SR χ R ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) (norm_movingSum_le χ R h) 2

theorem intOn_bdd {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : Measurable f) {s : Set α} (hs : MeasurableSet s) (hfin : μ s ≠ ⊤) (M : ℝ)
    (hb : ∀ x ∈ s, |f x| ≤ M) : IntegrableOn f s μ :=
  Measure.integrableOn_of_bounded hfin hf.aestronglyMeasurable
    ((ae_restrict_iff' hs).mpr (Eventually.of_forall fun x hx => by
      rw [Real.norm_eq_abs]; exact hb x hx))

/-- Integrability on a product box with `x + u ≤ R`. PROVED. -/
theorem Fm_int_prod {J I : Set ℝ} (hJ : MeasurableSet J) (hI : MeasurableSet I)
    (hJf : volume J ≠ ⊤) (hIf : volume I ≠ ⊤) {R : ℝ}
    (hR : ∀ x ∈ J, ∀ u ∈ I, x + u ≤ R) :
    Integrable (fun p : ℝ × ℝ => Fm χ p.1 p.2) ((volume.restrict J).prod (volume.restrict I)) := by
  rw [Measure.prod_restrict]
  refine intOn_bdd (Fm_measurable χ) (hJ.prod hI) ?_ (SR χ R ^ 2) ?_
  · rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hJf hIf
  · rintro ⟨x, u⟩ ⟨hx, hu⟩
    rw [abs_of_nonneg (Fm_nonneg χ _ _)]
    exact Fm_le χ (hR x hx u hu)

theorem Fm_int_x {J : Set ℝ} (hJ : MeasurableSet J) (hJf : volume J ≠ ⊤) {u R : ℝ}
    (hR : ∀ x ∈ J, x + u ≤ R) : IntegrableOn (fun x => Fm χ x u) J := by
  refine intOn_bdd ((Fm_measurable χ).comp (measurable_id.prodMk measurable_const)) hJ hJf
    (SR χ R ^ 2) fun x hx => ?_
  show |Fm χ x u| ≤ _
  rw [abs_of_nonneg (Fm_nonneg χ _ _)]
  exact Fm_le χ (hR x hx)

theorem Fm_int_u {I : Set ℝ} (hI : MeasurableSet I) (hIf : volume I ≠ ⊤) {x R : ℝ}
    (hR : ∀ u ∈ I, x + u ≤ R) : IntegrableOn (fun u => Fm χ x u) I := by
  refine intOn_bdd ((Fm_measurable χ).comp (measurable_const.prodMk measurable_id)) hI hIf
    (SR χ R ^ 2) fun u hu => ?_
  show |Fm χ x u| ≤ _
  rw [abs_of_nonneg (Fm_nonneg χ _ _)]
  exact Fm_le χ (hR u hu)

theorem windowMean_eq (N : ℕ) (u : ℝ) :
    windowMean N χ u = ∫ x in Ioc ((N : ℝ) / 2) (3 * N), Fm χ x u := rfl

/-- **The exchange of the integrals**: for `J ⊆ (N/2, 3N]` and `0 ≤ h ≤ N`,
`∫_J ∫_0^h |S(x, u)|² du dx ≤ ∫_0^h W(u) du`, `W = windowMean`. PROVED. -/
theorem swap_le (N : ℕ) {J : Set ℝ} (hJ : MeasurableSet J) (hJU : J ⊆ Ioc ((N : ℝ) / 2) (3 * N))
    {h : ℝ} (hhN : h ≤ N) :
    ∫ x in J, (∫ u in Ioc 0 h, Fm χ x u) ≤ ∫ u in Ioc 0 h, windowMean N χ u := by
  have hUf : volume (Ioc ((N : ℝ) / 2) (3 * N)) ≠ ⊤ := measure_Ioc_lt_top.ne
  have hJf : volume J ≠ ⊤ := ((measure_mono hJU).trans_lt measure_Ioc_lt_top).ne
  have hIf : volume (Ioc (0 : ℝ) h) ≠ ⊤ := measure_Ioc_lt_top.ne
  have hR : ∀ x ∈ Ioc ((N : ℝ) / 2) (3 * N), ∀ u ∈ Ioc (0 : ℝ) h, x + u ≤ 4 * N :=
    fun x hx u hu => by linarith [hx.2, hu.2]
  have hRJ : ∀ x ∈ J, ∀ u ∈ Ioc (0 : ℝ) h, x + u ≤ 4 * N := fun x hx => hR x (hJU hx)
  have iJ := Fm_int_prod χ hJ measurableSet_Ioc hJf hIf hRJ
  have iU := Fm_int_prod χ measurableSet_Ioc measurableSet_Ioc hUf hIf hR
  rw [integral_integral_swap (f := fun x u => Fm χ x u) iJ]
  simp_rw [windowMean_eq]
  refine integral_mono_ae iJ.integral_prod_right iU.integral_prod_right ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu => ?_)
  dsimp only
  exact setIntegral_mono_set
    (Fm_int_x χ measurableSet_Ioc hUf (R := 4 * N) fun x hx => by linarith [hx.2, hu.2])
    (Eventually.of_forall fun x => Fm_nonneg χ x u) (Eventually.of_forall hJU)

#print axioms Fm_int_prod
#print axioms swap_le

end
end LeanLab.PerelliPintz1992.Burst9

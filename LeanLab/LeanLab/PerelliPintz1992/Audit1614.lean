/-
Unit U-1614, run 20261104T0803Z-26516. Refutations of the old `farey_cover` and `gallagher_comparison`.
`gallagher_comparison`: `N = 16`, `M = 2`, `ξ = 1`, `ε = 1/2`, `A = -100`. Then the major arcs are empty,
the integral over `(15/16, 17/16)` is positive as `S(1) > 0`, and no modulus in `[2, 4]` has a Farey arc
near `1`, so `energy = 0`. The negative `A` is what the statement allows; it shows only that one block `M`
does not control the integral without a further hypothesis.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.Decomp97

namespace LeanLab.PerelliPintz1992.Audit1614
open Real ArithmeticFunction MeasureTheory Set Filter Topology Decomp97
attribute [local instance] Classical.propDecidable

/-- The old `farey_cover` is false at `N = 0`: `Q = 0`, so the union is empty, and `1/2` is a minor arc. -/
theorem old_farey_cover_false : ¬ ∀ (N : ℕ) (ε A : ℝ), ε = ε →
    minorArcs N A ⊆ ⋃ q ∈ Finset.Icc 1 ⌊Q N⌋₊, ⋃ (a : ℕ) (_ : a ≤ q ∧ a.Coprime q),
      Ioo ((a : ℝ) / q - 1 / (q * Q N)) ((a : ℝ) / q + 1 / (q * Q N)) := by
  intro h
  have hQ : Q 0 = 0 := by
    unfold Q
    norm_num
  have hmem : (1 / 2 : ℝ) ∈ minorArcs 0 0 := by
    unfold minorArcs
    refine ⟨by norm_num, ?_⟩
    unfold majorArcs L Bexp
    simp only [mem_iUnion, not_exists]
    rintro q ⟨hq1, hq⟩
    have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    norm_num at hq
    linarith
  have := h 0 0 0 rfl hmem
  simp only [mem_iUnion] at this
  obtain ⟨q, hq, -⟩ := this
  rw [hQ] at hq
  simp at hq

theorem Q16 : Q 16 = 2 := by
  unfold Q
  have : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  norm_num [this]

theorem H16 : H 16 (1 / 2) = 16 := by
  unfold H
  norm_num

theorem major_empty : majorArcs 16 (-100) = ∅ := by
  unfold majorArcs L Bexp
  apply eq_empty_of_forall_notMem
  intro x hx
  simp only [mem_iUnion] at hx
  obtain ⟨q, ⟨hq1, hq⟩, -⟩ := hx
  have hL : (1 : ℝ) < Real.log (16 : ℕ) := by
    have : Real.exp 1 < 16 := by linarith [Real.exp_one_lt_d9]
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    simpa using this
  have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have h2 : Real.log (16 : ℕ) ^ ((2 * (-100 : ℝ) + 100) / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hL (by norm_num)
  linarith

theorem minor_eq : minorArcs 16 (-100) = Ioo (1 / 2) (3 / 2) := by
  unfold minorArcs
  rw [major_empty, diff_empty]
  have : (((16 : ℕ) : ℝ) ^ (1 / 2 : ℝ) / 2) = 2 := by simpa [Q] using Q16
  rw [this]
  norm_num

theorem mem_filter_any {α : Type*} {p : α → Prop} (inst : DecidablePred p) {s : Finset α} {a : α}
    (h : a ∈ @Finset.filter α p inst s) : a ∈ s ∧ p a := Finset.mem_filter.mp h

theorem energy_zero : energy 16 (1 / 2) 1 2 = 0 := by
  have hY : Y 16 (1 / 2) 1 2 = ∅ := by
    unfold Y
    rw [Finset.eq_empty_iff_forall_notMem]
    intro q hq'
    obtain ⟨hq, h2, -, a, ha, hc, α, h3, h4⟩ := mem_filter_any _ hq'
    obtain ⟨⟨w, hw⟩, -, rfl⟩ := Finset.mem_image.mp hq
    have hfl : ⌊Q 16⌋₊ = 2 := by rw [Q16]; norm_num
    rw [hfl] at hw
    have hw2 := (Finset.mem_Icc.mp hw).2
    simp only [PNat.mk_coe] at h2 hc ha h3
    have hw' : w = 2 := by omega
    subst hw'
    have ha' := Finset.mem_Icc.mp ha
    have ha1 : a = 1 := by
      have : a = 1 ∨ a = 2 := by omega
      rcases this with h | h
      · exact h
      · subst h; norm_num at hc
    subst ha1
    rw [Q16, H16] at *
    norm_num at h3 h4
    have := (abs_le.mp h3).2
    have := (abs_lt.mp h4).1
    linarith
  unfold energy
  rw [hY]
  simp

theorem S_one_pos : 0 < ‖S 16 1‖ ^ 2 := by
  have h : S 16 1 = ((∑ n ∈ Finset.Icc 16 (2 * 16), Λ n : ℝ) : ℂ) := by
    unfold S e
    push_cast
    apply Finset.sum_congr rfl
    intro n _
    have h1 : Complex.exp (2 * π * Complex.I * ((n : ℂ) * 1)) = 1 := by
      have h2 := Complex.exp_nat_mul_two_pi_mul_I n
      rwa [show 2 * π * Complex.I * ((n : ℂ) * 1) = n * (2 * π * Complex.I) by ring]
    simp only [mul_one] at h1 ⊢
    rw [h1, mul_one]
  rw [h, Complex.norm_real]
  have hp : 0 < ∑ n ∈ Finset.Icc 16 (2 * 16), Λ n := by
    apply Finset.sum_pos' (fun n _ => vonMangoldt_nonneg)
    refine ⟨17, by simp, ?_⟩
    rw [vonMangoldt_apply_prime (by norm_num)]
    exact Real.log_pos (by norm_num)
  have : 0 < ‖∑ n ∈ Finset.Icc 16 (2 * 16), Λ n‖ := norm_pos_iff.mpr hp.ne'
  positivity

theorem S_cont : Continuous fun α : ℝ => ‖S 16 α‖ ^ 2 := by
  unfold S e
  fun_prop

/-- The old `gallagher_comparison` is false. -/
theorem old_gallagher_comparison_false :
    ¬ ∀ (N : ℕ) (ε ξ A : ℝ) (M : ℕ), 1 ≤ M → (M : ℝ) ≤ Q N →
      (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A, ‖S N α‖ ^ 2)
        ≤ 2 * (energy N ε ξ M) := by
  intro h
  have := h 16 (1 / 2) 1 (-100) 2 (by norm_num) (by rw [Q16]; norm_num)
  rw [energy_zero, minor_eq, H16] at this
  have hs : Ioo ((1 : ℝ) - 1 / 16) (1 + 1 / 16) ∩ Ioo (1 / 2) (3 / 2) = Ioo (15 / 16) (17 / 16) := by
    ext x
    simp only [mem_inter_iff, mem_Ioo]
    constructor
    · rintro ⟨⟨h1, h2⟩, -⟩
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  rw [hs, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)] at this
  have hpos : 0 < ∫ α in (15 / 16 : ℝ)..(17 / 16), ‖S 16 α‖ ^ 2 :=
    intervalIntegral.integral_pos (by norm_num) S_cont.continuousOn
      (fun _ _ => by positivity) ⟨1, ⟨by norm_num, by norm_num⟩, S_one_pos⟩
  linarith

end LeanLab.PerelliPintz1992.Audit1614
#print axioms LeanLab.PerelliPintz1992.Audit1614.old_farey_cover_false
#print axioms LeanLab.PerelliPintz1992.Audit1614.old_gallagher_comparison_false

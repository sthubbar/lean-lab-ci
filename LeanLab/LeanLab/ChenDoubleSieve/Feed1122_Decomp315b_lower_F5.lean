import LeanLab.ChenDoubleSieve.Feed1122_Decomp315b_lower_F4
import LeanLab.ChenDoubleSieve.Decomp348c

/-!
Feed split of `lower_F5` in `Decomp315b`, Wu 2004 Section 10, page 39, equation 10.5.
Source: https://arxiv.org/pdf/0705.1652, pages 38 to 42.
Same scheme as `lower_F4`: linear sieve on each `A_{pq}` at level `N^{1/2}/(pq)`,
then prime pair sum to double integral, with the shared Mertens main term.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task315.Feed1122F0
open Task275
open Wu41 (S PS)
open Wu08Sum (P2 P4)
open Wu04Functional (IsLinearSieve IsBuchstab)
open LeanLab.ChenDoubleSieve.Task315.FeedS120

/-- The pair weight sum of the F5 term of equation 10.5, over
`N^{κ₁} ≤ p < N^{κ₂} ≤ q < N^{1/2 - 2κ₁}/p`. -/
def pairSum5 (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ kappa2 ∧
      (N : ℝ) ^ kappa2 ≤ q ∧ (q : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / p),
    f ((1 / 2 - Real.log q.1 / Real.log N - Real.log q.2 / Real.log N) / kappa1) /
      (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1))

/-- Membership in the F5 pair band of equation 10.5. -/
theorem pairs5_mem (N : ℕ) : ∀ q ∈ Task348.lowerPairs5 N, q.1.Prime ∧ q.2.Prime ∧
    (N : ℝ) ^ kappa1 ≤ q.1 ∧ (q.1 : ℝ) < (N : ℝ) ^ kappa2 ∧ (N : ℝ) ^ kappa2 ≤ q.2 ∧
      (q.2 : ℝ) * q.1 < (N : ℝ) ^ (1 / 2 - 2 * kappa1) := by
  intro q hq
  simp only [Task348.lowerPairs5, Wu08Sum.P2, Finset.mem_filter] at hq
  obtain ⟨-, hp1, hp2, -, -, hlo, hlt, hlo2, hhi⟩ := hq
  have hp0 : (0 : ℝ) < q.1 := by exact_mod_cast hp1.pos
  exact ⟨hp1, hp2, hlo, hlt, hlo2, (lt_div_iff₀ hp0).1 hhi⟩

/-- The pair band of equation 10.5 for F5 keeps the limiting argument in `[2, 4]`. -/
theorem pairs5_window (N : ℕ) (hN2 : 2 ≤ N) : ∀ q ∈ Task348.lowerPairs5 N,
    q.1.Prime ∧ q.2.Prime ∧ q.1 ≠ q.2 ∧
      (2 : ℝ) ≤ ((1 / 2 : ℝ) - Real.log (q.1 : ℝ) / Real.log N
          - Real.log (q.2 : ℝ) / Real.log N) / kappa1 ∧
      ((1 / 2 : ℝ) - Real.log (q.1 : ℝ) / Real.log N
          - Real.log (q.2 : ℝ) / Real.log N) / kappa1 ≤ 4 := by
  intro q hq
  obtain ⟨hp1, hp2, hlo, hlt, hlo2, hhi⟩ := pairs5_mem N q hq
  have hk1 : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hk1v : kappa1 = 1 / 12 := rfl
  have hk2v : kappa2 = 29 / 250 := rfl
  have hp0 : (0 : ℝ) < q.1 := by exact_mod_cast hp1.pos
  have hq0 : (0 : ℝ) < q.2 := by exact_mod_cast hp2.pos
  have a1 := le_logdiv hN2 hlo
  have a2 := le_logdiv hN2 hlo2
  have b := logdiv_lt hN2 (by positivity) hhi
  rw [Real.log_mul hq0.ne' hp0.ne', add_div] at b
  have hne : q.1 ≠ q.2 := by
    intro hpq
    have : (q.1 : ℝ) < q.2 := lt_of_lt_of_le hlt hlo2
    rw [hpq] at this
    exact lt_irrefl _ this
  refine ⟨hp1, hp2, hne, ?_, ?_⟩
  · rw [le_div_iff₀ hk1]; linarith
  · rw [div_le_iff₀ hk1]; linarith

/-- The pair weights of the F5 band have bounded sum, by Mertens in band form. -/
theorem pairs5_weight : ∃ C : ℝ, ∀ᶠ N : ℕ in Filter.atTop,
    ∑ q ∈ Task348.lowerPairs5 N, 1 / (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1)) ≤ C := by
  obtain ⟨C1, hC1, hb1⟩ := band_recip_bound kappa1 kappa2 (by norm_num [kappa1])
    (by norm_num [kappa1, kappa2])
  obtain ⟨C2, hC2, hb2⟩ := band_recip_bound kappa2 (1 / 2 - 2 * kappa1) (by norm_num [kappa2])
    (by norm_num [kappa1, kappa2])
  refine ⟨4 * (C1 * C2), ?_⟩
  filter_upwards [hb1, hb2, Filter.eventually_ge_atTop 2] with N hb1 hb2 hN2
  refine (pair_weight_le _ fun q hq => ?_).trans ?_
  · obtain ⟨h1, h2, -⟩ := pairs5_mem N q hq
    exact ⟨h1.two_le, h2.two_le⟩
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply mul_le_mul _ _ (Finset.sum_nonneg fun _ _ => by positivity) hC1
    · apply hb1
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨h1, -, hlo, hlt, -⟩ := pairs5_mem N q hq
      exact ⟨h1, hlo, hlt.le⟩
    · apply hb2
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨h1, h2, -, -, hlo2, hhi⟩ := pairs5_mem N q hq
      have hp1 : (1 : ℝ) ≤ q.1 := by exact_mod_cast h1.one_le
      have hq0 : (0 : ℝ) ≤ q.2 := by positivity
      refine ⟨h2, hlo2, ?_⟩
      nlinarith

/-- LEAF: Wu 2004 page 39, proof of equation 10.5 for F5, the linear sieve lower bound applied
to each `A_{pq}` at level `N^{1/2}/(pq)` and sifting limit `N^{κ₁}`, summed over the pairs,
remainders by Bombieri Vinogradov. Class HARD. -/
theorem sieve_lower5 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ e : ℝ, 0 < e → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      mainXV N * pairSum5 f N - e * Θ N ≤ sieveTerms N 5 := by
  intro e he
  set c := 2 / (kappa1 * exp eulerMascheroniConstant) with hcdef
  have hc : 0 < c := by rw [hcdef]; unfold kappa1; positivity
  obtain ⟨B, _hB, N1, h1⟩ := Task348.main5_lower F f h (e / 2) (by positivity)
  obtain ⟨N2, h2⟩ := mertens_main_term 1 one_pos
  obtain ⟨C, hW⟩ := pairs5_weight
  obtain ⟨N3, h3⟩ := pair_shift_small f h.2.1 B 2 4 (by norm_num) Task348.lowerPairs5
    pairs5_window C hW (e / (2 * (c + 1))) (by positivity)
  refine ⟨max 2 (max N1 (max N2 N3)), fun N hN hle => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hle
  have hθ := Θ_pos hN2
  have hm := h1 N hN (by omega)
  have hM := h2 N hN (by omega)
  have hd := h3 N (by omega)
  have hmain : Task348.main5 f B N = mainXV N * Task348.lowerSum5 f B N := rfl
  have hP : pairSum5 f N = ∑ q ∈ Task348.lowerPairs5 N,
      f (((1 / 2 : ℝ) - Real.log (q.1 : ℝ) / Real.log N
          - Real.log (q.2 : ℝ) / Real.log N) / kappa1) /
            (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1)) := rfl
  have hL : Task348.lowerSum5 f B N = ∑ q ∈ Task348.lowerPairs5 N,
      f (Task348.lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ) := rfl
  rw [hmain] at hm
  rw [← hP, ← hL] at hd
  have hX : mainXV N = ((N : ℝ) / Real.log N) *
      ∏ p ∈ PS N 0 ((N : ℝ) ^ kappa1), (1 - 1 / ((p : ℝ) - 1)) := rfl
  rw [← hX, one_mul] at hM
  have hXabs : |mainXV N| ≤ (c + 1) * Θ N := by
    have := abs_sub_abs_le_abs_sub (mainXV N) (c * Θ N)
    rw [abs_of_pos (by positivity : 0 < c * Θ N)] at this
    linarith
  set d := pairSum5 f N - Task348.lowerSum5 f B N
  have hprod : mainXV N * d ≤ e / 2 * Θ N := by
    have k1 : mainXV N * d ≤ |mainXV N| * |d| := by
      rw [← abs_mul]; exact le_abs_self _
    have k2 : |mainXV N| * |d| ≤ (c + 1) * Θ N * (e / (2 * (c + 1))) :=
      mul_le_mul hXabs hd (abs_nonneg _) (by positivity)
    have k3 : (c + 1) * Θ N * (e / (2 * (c + 1))) = e / 2 * Θ N := by
      field_simp
    linarith
  have : mainXV N * pairSum5 f N = mainXV N * Task348.lowerSum5 f B N + mainXV N * d := by
    simp only [d]; ring
  linarith

/-- LEAF: Wu 2004 page 39, equation 10.5 main term for F5, the prime pair sum tends to
`∫_{κ₁}^{κ₂} ∫_{κ₂}^{1/2 - 2κ₁ - t} f((1/2 - t - u)/κ₁) du/u dt/t`, by the prime number
theorem with partial summation and continuity of `f`. Class MEDIUM. -/
theorem pair_sum5_limit (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ e : ℝ, 0 < e → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      |pairSum5 f N - ∫ t in kappa1..kappa2,
        (∫ u in kappa2..(1 / 2 - 2 * kappa1 - t), f ((1 / 2 - t - u) / kappa1) / u) / t| ≤ e := by
  intro e he
  obtain ⟨C, hW⟩ := pairs5_weight
  obtain ⟨N3, h3⟩ := pair_shift_small f h.2.1 1 2 4 (by norm_num) Task348.lowerPairs5
    pairs5_window C hW (e / 2) (by positivity)
  have hT := (Metric.tendsto_nhds.1 (Task348.lowerSum5_tendsto F f h 1 one_pos)) (e / 2)
    (by positivity)
  rw [Task348.evenAtTop, Filter.eventually_inf_principal] at hT
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hT
  refine ⟨max N3 K, fun N hN hle => ?_⟩
  have hd := h3 N (le_trans (le_max_left _ _) hle)
  have hk := hK N (le_trans (le_max_right _ _) hle) hN
  rw [Real.dist_eq] at hk
  have hP : pairSum5 f N = ∑ q ∈ Task348.lowerPairs5 N,
      f (((1 / 2 : ℝ) - Real.log (q.1 : ℝ) / Real.log N
          - Real.log (q.2 : ℝ) / Real.log N) / kappa1) /
            (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1)) := rfl
  have hL : Task348.lowerSum5 f 1 N = ∑ q ∈ Task348.lowerPairs5 N,
      f (Task348.lowerLevel 1 N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ) := rfl
  rw [← hP, ← hL] at hd
  have hI : Task348.lowerIntegral5 f = ∫ t in kappa1..kappa2,
      (∫ u in kappa2..(1 / 2 - 2 * kappa1 - t), f ((1 / 2 - t - u) / kappa1) / u) / t := rfl
  rw [hI] at hk
  calc _ = |(pairSum5 f N - Task348.lowerSum5 f 1 N) + (Task348.lowerSum5 f 1 N -
        ∫ t in kappa1..kappa2, (∫ u in kappa2..(1 / 2 - 2 * kappa1 - t),
          f ((1 / 2 - t - u) / kappa1) / u) / t)| := by
        rw [sub_add_sub_cancel]
    _ ≤ _ := abs_add_le _ _
    _ ≤ e / 2 + e / 2 := add_le_add hd hk.le
    _ = e := by ring

theorem lower_F5_of_leaves (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 5 - ε) * Θ N ≤ sieveTerms N 5 := by
  have hI : integralTerms F f ω 5 = 2 / (kappa1 * exp eulerMascheroniConstant) *
      ∫ t in kappa1..kappa2, (∫ u in kappa2..(1 / 2 - 2 * kappa1 - t),
        f ((1 / 2 - t - u) / kappa1) / u) / t := rfl
  rw [hI]
  exact eventual_prod (fun N => sieveTerms N 5) mainXV (pairSum5 f) _ _
    (by unfold kappa1; positivity) (sieve_lower5 F f ω h hω) mertens_main_term
    (pair_sum5_limit F f h)

end LeanLab.ChenDoubleSieve.Task315.Feed1122F0

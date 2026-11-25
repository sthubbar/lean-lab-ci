import LeanLab.ChenDoubleSieve.Feed1122_Decomp315b_lower_F0
import LeanLab.ChenDoubleSieve.Feed1122_S120_PairShift

/-!
Feed split of `lower_F4` in `Decomp315b`, Wu 2004 Section 10, page 39, equation 10.5.
Source: https://arxiv.org/pdf/0705.1652, pages 38 to 42.
For each pair `p < q` the set `A_{pq}` is sifted by the linear sieve at level
`N^{1/2}/(pq)` with `s = (1/2 - t - u)/κ₁`, `p = N^t`, `q = N^u`; summing gives the
sieve leaf, and the prime sum is turned into the double integral by the prime number
theorem in the form of Mertens. The Mertens main term is shared with `lower_F0`.
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

/-- Pointwise algebra for a product main term. -/
theorem alg_prod (x m s θ c J e e2 e3 : ℝ) (hθ : 0 ≤ θ) (hc : 0 ≤ c) (he2 : 0 ≤ e2)
    (hA : m * s - e * θ ≤ x) (hM : |m - c * θ| ≤ e2 * θ) (hS : |s - J| ≤ e3) :
    c * J * θ - e * θ - e2 * θ * (|J| + e3) - c * e3 * θ ≤ x := by
  have hs : |s| ≤ |J| + e3 := by
    have := abs_sub_abs_le_abs_sub s J
    linarith
  have h1 : |(m - c * θ) * s| ≤ e2 * θ * (|J| + e3) := by
    rw [abs_mul]
    exact mul_le_mul hM hs (abs_nonneg _) (by positivity)
  have h2 : |c * θ * (s - J)| ≤ c * θ * e3 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ c * θ)]
    exact mul_le_mul_of_nonneg_left hS (by positivity)
  have h1' := (abs_le.mp h1).1
  have h2' := (abs_le.mp h2).1
  have : m * s - c * J * θ = (m - c * θ) * s + c * θ * (s - J) := by ring
  nlinarith

/-- Eventual form of `alg_prod`, used for the pair and quadruple sums. -/
theorem eventual_prod (x M s : ℕ → ℝ) (c J : ℝ) (hc : 0 ≤ c)
    (hA : ∀ e : ℝ, 0 < e → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      M N * s N - e * Θ N ≤ x N)
    (hM : ∀ e : ℝ, 0 < e → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      |M N - c * Θ N| ≤ e * Θ N)
    (hS : ∀ e : ℝ, 0 < e → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N → |s N - J| ≤ e) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (c * J - ε) * Θ N ≤ x N := by
  intro ε hε
  set e3 := min 1 (ε / (3 * (c + 1)))
  set e2 := ε / (3 * (|J| + 2))
  have he3 : 0 < e3 := lt_min one_pos (by positivity)
  have he2 : 0 < e2 := by positivity
  obtain ⟨N1, h1⟩ := hA (ε / 3) (by positivity)
  obtain ⟨N2, h2⟩ := hM e2 he2
  obtain ⟨N3, h3⟩ := hS e3 he3
  refine ⟨max N1 (max N2 N3), fun N hN hle => ?_⟩
  have k := alg_prod (x N) (M N) (s N) (Θ N) c J (ε / 3) e2 e3 (Θ_nonneg N) hc he2.le
    (h1 N hN (by omega)) (h2 N hN (by omega)) (h3 N hN (by omega))
  have hθ := Θ_nonneg N
  have he3le : e3 ≤ 1 := min_le_left _ _
  have he3le' : e3 ≤ ε / (3 * (c + 1)) := min_le_right _ _
  have q1 : e2 * (|J| + e3) ≤ ε / 3 := by
    have hJ := abs_nonneg J
    have : e2 * (|J| + e3) ≤ e2 * (|J| + 2) := by nlinarith
    have : e2 * (|J| + 2) = ε / 3 := by unfold e2; field_simp
    linarith
  have q2 : c * e3 ≤ ε / 3 := by
    have : c * e3 ≤ c * (ε / (3 * (c + 1))) := mul_le_mul_of_nonneg_left he3le' hc
    have : c * (ε / (3 * (c + 1))) ≤ ε / 3 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have e1 : e2 * Θ N * (|J| + e3) ≤ ε / 3 * Θ N := by nlinarith
  have e4 : c * e3 * Θ N ≤ ε / 3 * Θ N := by nlinarith
  nlinarith

/-- The sifting main term `X V(N^{κ₁})` of Section 10. -/
def mainXV (N : ℕ) : ℝ :=
  ((N : ℝ) / Real.log N) * ∏ p ∈ PS N 0 ((N : ℝ) ^ kappa1), (1 - 1 / ((p : ℝ) - 1))

/-- The pair weight sum `∑ f(s_{pq}) / ((p - 1)(q - 1))` of equation 10.5,
`s_{pq} = (1/2 - log p / log N - log q / log N) / κ₁`. -/
def pairSum4 (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2),
    f ((1 / 2 - Real.log q.1 / Real.log N - Real.log q.2 / Real.log N) / kappa1) /
      (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1))

/-- The pair band of equation 10.5 for F4 keeps the limiting argument in `[3, 4]`. -/
theorem pairs4_window (N : ℕ) (hN2 : 2 ≤ N) : ∀ q ∈ Task348.lowerPairs4 N,
    q.1.Prime ∧ q.2.Prime ∧ q.1 ≠ q.2 ∧
      (3 : ℝ) ≤ ((1 / 2 : ℝ) - Real.log (q.1 : ℝ) / Real.log N
          - Real.log (q.2 : ℝ) / Real.log N) / kappa1 ∧
      ((1 / 2 : ℝ) - Real.log (q.1 : ℝ) / Real.log N
          - Real.log (q.2 : ℝ) / Real.log N) / kappa1 ≤ 4 := by
  intro q hq
  simp only [Task348.lowerPairs4, Wu08Sum.P2, Finset.mem_filter] at hq
  obtain ⟨-, hp1, hp2, -, -, hlo, hlt, hhi⟩ := hq
  have hk1 : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hk1v : kappa1 = 1 / 12 := rfl
  have hk2v : kappa2 = 29 / 250 := rfl
  have hlt' : (q.1 : ℝ) < q.2 := by exact_mod_cast hlt
  have a1 := le_logdiv hN2 hlo
  have a2 := le_logdiv hN2 (hlo.trans hlt'.le)
  have b2 := logdiv_lt hN2 (by exact_mod_cast hp2.pos) hhi
  have b1 := logdiv_lt hN2 (by exact_mod_cast hp1.pos) (hlt'.trans hhi)
  refine ⟨hp1, hp2, hlt.ne, ?_, ?_⟩
  · rw [le_div_iff₀ hk1]; linarith
  · rw [div_le_iff₀ hk1]; linarith

/-- The pair weights of the F4 band have bounded sum, by Mertens in band form. -/
theorem pairs4_weight : ∃ C : ℝ, ∀ᶠ N : ℕ in Filter.atTop,
    ∑ q ∈ Task348.lowerPairs4 N, 1 / (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1)) ≤ C := by
  obtain ⟨C1, hC1, hb⟩ := band_recip_bound kappa1 kappa2 (by norm_num [kappa1])
    (by norm_num [kappa1, kappa2])
  refine ⟨4 * (C1 * C1), ?_⟩
  filter_upwards [hb, Filter.eventually_ge_atTop 2] with N hb hN2
  have mem : ∀ q ∈ Task348.lowerPairs4 N, q.1.Prime ∧ q.2.Prime ∧
      (N : ℝ) ^ kappa1 ≤ q.1 ∧ (q.1 : ℝ) < q.2 ∧ (q.2 : ℝ) < (N : ℝ) ^ kappa2 := by
    intro q hq
    simp only [Task348.lowerPairs4, Wu08Sum.P2, Finset.mem_filter] at hq
    obtain ⟨-, hp1, hp2, -, -, hlo, hlt, hhi⟩ := hq
    exact ⟨hp1, hp2, hlo, by exact_mod_cast hlt, hhi⟩
  refine (pair_weight_le _ fun q hq => ?_).trans ?_
  · obtain ⟨h1, h2, -⟩ := mem q hq
    exact ⟨h1.two_le, h2.two_le⟩
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply mul_le_mul _ _ (Finset.sum_nonneg fun _ _ => by positivity) hC1
    · apply hb
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨h1, -, hlo, hlt, hhi⟩ := mem q hq
      exact ⟨h1, hlo, (hlt.trans hhi).le⟩
    · apply hb
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨-, h2, hlo, hlt, hhi⟩ := mem q hq
      exact ⟨h2, hlo.trans hlt.le, hhi.le⟩

/-- LEAF: Wu 2004 page 39, proof of equation 10.5, the linear sieve lower bound applied to each
`A_{pq}` at level `N^{1/2}/(pq)` and sifting limit `N^{κ₁}`, `|A_{pq}| ≈ X/((p-1)(q-1))`,
summed over the pairs with the remainders bounded by Bombieri Vinogradov. Class HARD. -/
theorem sieve_lower4 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ e : ℝ, 0 < e → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      mainXV N * pairSum4 f N - e * Θ N ≤ sieveTerms N 4 := by
  intro e he
  set c := 2 / (kappa1 * exp eulerMascheroniConstant) with hcdef
  have hc : 0 < c := by rw [hcdef]; unfold kappa1; positivity
  obtain ⟨B, _hB, N1, h1⟩ := Task348.main4_lower F f h (e / 2) (by positivity)
  obtain ⟨N2, h2⟩ := mertens_main_term 1 one_pos
  obtain ⟨C, hW⟩ := pairs4_weight
  obtain ⟨N3, h3⟩ := pair_shift_small f h.2.1 B 3 4 (by norm_num) Task348.lowerPairs4
    pairs4_window C hW (e / (2 * (c + 1))) (by positivity)
  refine ⟨max 2 (max N1 (max N2 N3)), fun N hN hle => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hle
  have hθ := Θ_pos hN2
  have hm := h1 N hN (by omega)
  have hM := h2 N hN (by omega)
  have hd := h3 N (by omega)
  have hmain : Task348.main4 f B N = mainXV N * Task348.lowerSum4 f B N := rfl
  have hP : pairSum4 f N = ∑ q ∈ Task348.lowerPairs4 N,
      f (((1 / 2 : ℝ) - Real.log (q.1 : ℝ) / Real.log N
          - Real.log (q.2 : ℝ) / Real.log N) / kappa1) /
            (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1)) := rfl
  have hL : Task348.lowerSum4 f B N = ∑ q ∈ Task348.lowerPairs4 N,
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
  set d := pairSum4 f N - Task348.lowerSum4 f B N
  have hprod : mainXV N * d ≤ e / 2 * Θ N := by
    have k1 : mainXV N * d ≤ |mainXV N| * |d| := by
      rw [← abs_mul]; exact le_abs_self _
    have k2 : |mainXV N| * |d| ≤ (c + 1) * Θ N * (e / (2 * (c + 1))) :=
      mul_le_mul hXabs hd (abs_nonneg _) (by positivity)
    have k3 : (c + 1) * Θ N * (e / (2 * (c + 1))) = e / 2 * Θ N := by
      field_simp
    linarith
  have : mainXV N * pairSum4 f N = mainXV N * Task348.lowerSum4 f B N + mainXV N * d := by
    simp only [d]; ring
  linarith

/-- LEAF: Wu 2004 page 39, equation 10.5 main term, the prime pair sum tends to the double
integral `∫_{κ₁}^{κ₂} ∫_t^{κ₂} f((1/2 - t - u)/κ₁) du/u dt/t`, by the prime number theorem
with partial summation and continuity of `f`. Class MEDIUM. -/
theorem pair_sum4_limit (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ e : ℝ, 0 < e → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      |pairSum4 f N - ∫ t in kappa1..kappa2,
        (∫ u in t..kappa2, f ((1 / 2 - t - u) / kappa1) / u) / t| ≤ e := by
  intro e he
  obtain ⟨C, hW⟩ := pairs4_weight
  obtain ⟨N3, h3⟩ := pair_shift_small f h.2.1 1 3 4 (by norm_num) Task348.lowerPairs4
    pairs4_window C hW (e / 2) (by positivity)
  have hT := (Metric.tendsto_nhds.1 (Task348.lowerSum4_tendsto F f h 1 one_pos)) (e / 2)
    (by positivity)
  rw [Task348.evenAtTop, Filter.eventually_inf_principal] at hT
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hT
  refine ⟨max N3 K, fun N hN hle => ?_⟩
  have hd := h3 N (le_trans (le_max_left _ _) hle)
  have hk := hK N (le_trans (le_max_right _ _) hle) hN
  rw [Real.dist_eq] at hk
  have hP : pairSum4 f N = ∑ q ∈ Task348.lowerPairs4 N,
      f (((1 / 2 : ℝ) - Real.log (q.1 : ℝ) / Real.log N
          - Real.log (q.2 : ℝ) / Real.log N) / kappa1) /
            (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1)) := rfl
  have hL : Task348.lowerSum4 f 1 N = ∑ q ∈ Task348.lowerPairs4 N,
      f (Task348.lowerLevel 1 N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ) := rfl
  rw [← hP, ← hL] at hd
  have hI : Task348.lowerIntegral4 f = ∫ t in kappa1..kappa2,
      (∫ u in t..kappa2, f ((1 / 2 - t - u) / kappa1) / u) / t := rfl
  rw [hI] at hk
  calc _ = |(pairSum4 f N - Task348.lowerSum4 f 1 N) + (Task348.lowerSum4 f 1 N -
        ∫ t in kappa1..kappa2, (∫ u in t..kappa2, f ((1 / 2 - t - u) / kappa1) / u) / t)| := by
        rw [sub_add_sub_cancel]
    _ ≤ _ := abs_add_le _ _
    _ ≤ e / 2 + e / 2 := add_le_add hd hk.le
    _ = e := by ring

theorem lower_F4_of_leaves (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 4 - ε) * Θ N ≤ sieveTerms N 4 := by
  have hI : integralTerms F f ω 4 = 2 / (kappa1 * exp eulerMascheroniConstant) *
      ∫ t in kappa1..kappa2, (∫ u in t..kappa2, f ((1 / 2 - t - u) / kappa1) / u) / t := rfl
  rw [hI]
  exact eventual_prod (fun N => sieveTerms N 4) mainXV (pairSum4 f) _ _
    (by unfold kappa1; positivity) (sieve_lower4 F f ω h hω) mertens_main_term
    (pair_sum4_limit F f h)

end LeanLab.ChenDoubleSieve.Task315.Feed1122F0

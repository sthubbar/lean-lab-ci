/-
Burst 20261122, unit P1122-0105, the QUESTION check on the LEAF `upper_slack_split_slack_distribution`
of SPLIT_upper_slack_split_rescaled_short_distribution, P0069 Baker Harman Pintz 1997, page 53 with
display 5.17 on page 51. That LEAF asks the short distribution condition at one fixed density
v = w(1/c4)/c4 + deleted integral + delta for EVERY bounded rescaling lam that is at least one on J.
Applied at the two constant rescalings lam = 1 and lam = 2 it fails: with q = 1, the trivial
character and t = 2Y, the two centered sums differ by the plain raw sum, and twice the first minus
the second is the main term v times the length of J over log Y, of size Y over log x, while each
error is Y over log x squared. No prime count is needed, only v > 0 and the length of J.
Result: the LEAF implies that its own cited inputs, Theorem 4 and Lemma 9, are not both true, so it
is either false or vacuous. The statement of the LEAF is not changed; this file only adds the
refutation. New file, no new definition, no sorry.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_upper_slack_split_rescaled_short_distribution

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- The trivial character modulo one is one at every residue. -/
theorem refute1122_chi_one (m : ℕ) : (1 : DirichletCharacter ℂ 1) (m : ZMod 1) = 1 := by
  rw [Subsingleton.elim (m : ZMod 1) 1, map_one]

/-- P0069 page 3, condition iii with q = 1 and t = 2Y, evaluated for a constant rescaling `L`:
the centered sum is the real number `L` times the raw sum over J minus the length of J times
`v / log Y`. -/
theorem refute1122_centered_sum {ε x : ℝ} (hY : 2 ≤ x ^ (11 / 20 + ε)) (L v : ℝ) :
    (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ 2 * x ^ (11 / 20 + ε)),
        (((upperNormCoeff ε (fun _ _ => L) x m : ℝ) : ℂ) * (1 : DirichletCharacter ℂ 1) (m : ZMod 1) -
          Thm2.delta (1 : DirichletCharacter ℂ 1) * v / Real.log (x ^ (11 / 20 + ε)))) =
      (((∑ m ∈ rightInterval ε x, (L * upperRawWeight ε (x ^ (11 / 20 + ε)) m -
          v / Real.log (x ^ (11 / 20 + ε)))) : ℝ) : ℂ) := by
  rw [Finset.filter_true_of_mem]
  · push_cast
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [refute1122_chi_one]
    simp only [Thm2.delta, upperNormCoeff, hY, hm, and_self, ↓reduceIte]
    push_cast
    ring
  · intro m hm
    have hk := (Finset.mem_Ioc.mp hm).2
    have h0 : (0 : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by linarith
    calc (m : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by exact_mod_cast hk
      _ ≤ _ := Nat.floor_le h0

/-- The length of J is at least half of Y once Y is at least two. -/
theorem refute1122_card_ge {ε x : ℝ} (hY : 2 ≤ x ^ (11 / 20 + ε)) :
    x ^ (11 / 20 + ε) / 2 ≤ ((rightInterval ε x).card : ℝ) := by
  set Y := x ^ (11 / 20 + ε) with hYdef
  have hle : ⌊Y⌋₊ ≤ ⌊2 * Y⌋₊ := Nat.floor_le_floor (by linarith)
  have hc : (rightInterval ε x).card = ⌊2 * Y⌋₊ - ⌊Y⌋₊ := by
    simp only [rightInterval, Nat.card_Ioc, hYdef]
  rw [hc, Nat.cast_sub hle]
  have h1 : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have h2 : 2 * Y < (⌊2 * Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  linarith

/-- The QUESTION check of unit P1122-0105, the core: for a positive density `v` the short
distribution condition of P0069 page 3, condition iii, cannot hold both for the normalized
coefficient with `lam = 1` and with `lam = 2`. PROVED. -/
theorem upper_slack_short_distribution_two_scalings_absurd
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {v : ℝ} (hv : 0 < v)
    (h1 : Task308.ShortDistribution ε v (upperNormCoeff ε (fun _ _ => 1)))
    (h2 : Task308.ShortDistribution ε v (upperNormCoeff ε (fun _ _ => 2))) : False := by
  obtain ⟨C1, hC1⟩ := h1 2 two_pos
  obtain ⟨C2, hC2⟩ := h2 2 two_pos
  set K := C2 + 2 * C1 with hK
  have hKv : 0 ≤ 2 * |K| / v := by positivity
  set T : ℝ := |C1| + |C2| + 4 + 2 * |K| / v with hT
  have hA1 := abs_nonneg C1
  have hA2 := abs_nonneg C2
  have hT4 : 4 ≤ T := by linarith
  set x := Real.exp T with hx
  have hxT : T + 1 ≤ x := Real.add_one_le_exp T
  have hlog : Real.log x = T := Real.log_exp T
  have hx4 : 4 ≤ x := by linarith
  have hxC1 : C1 ≤ x := by linarith [le_abs_self C1]
  have hxC2 : C2 ≤ x := by linarith [le_abs_self C2]
  have hY2 : 2 ≤ x ^ (11 / 20 + ε) := upper_Y_ge_two hε hx4
  set Y := x ^ (11 / 20 + ε) with hYdef
  have hq : ((1 : ℕ) : ℝ) ≤ Real.log x ^ (2 : ℝ) := by
    rw [hlog, Nat.cast_one]
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have e1 := hC1 x hxC1 1 le_rfl hq 1 (2 * Y) le_rfl
  have e2 := hC2 x hxC2 1 le_rfl hq 1 (2 * Y) le_rfl
  rw [refute1122_centered_sum hY2, Complex.norm_real, Real.norm_eq_abs] at e1 e2
  set R := ∑ m ∈ rightInterval ε x, upperRawWeight ε Y m with hR
  set N : ℝ := ((rightInterval ε x).card : ℝ) with hN
  set w := v / Real.log Y with hw
  have hs : ∀ L : ℝ, (∑ m ∈ rightInterval ε x, (L * upperRawWeight ε Y m - w)) = L * R - N * w := by
    intro L
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  rw [hs] at e1 e2
  have hTpos : 0 < T := by linarith
  have hpow : Real.log x ^ (-2 : ℝ) = (T ^ 2)⁻¹ := by
    rw [hlog, Real.rpow_neg hTpos.le, Real.rpow_two]
  rw [hpow] at e1 e2
  have hYpos : 0 < Y := by linarith
  -- the main term is bounded by the two errors
  have hmain : N * w ≤ K * Y * (T ^ 2)⁻¹ := by
    have a1 := (abs_le.mp e1).1
    have a2 := (abs_le.mp e2).2
    rw [hK]
    nlinarith
  -- lower bounds for N and w
  have hNge : Y / 2 ≤ N := refute1122_card_ge hY2
  have hlogY : Real.log Y = (11 / 20 + ε) * T := by
    rw [hYdef, Real.log_rpow (by linarith), hlog]
  have hθ1 : 11 / 20 + ε ≤ 1 := by
    have : (1 : ℝ) / 10 ^ 8 ≤ 9 / 20 := by norm_num
    linarith
  have hθ0 : 0 < 11 / 20 + ε := by linarith
  have hwge : v / T ≤ w := by
    rw [hw, hlogY]
    apply div_le_div_of_nonneg_left hv.le (by positivity)
    nlinarith
  have hvT : 0 < v / T := by positivity
  have hlow : Y / 2 * (v / T) ≤ N * w :=
    mul_le_mul hNge hwge hvT.le (by linarith)
  have hcomb : Y / 2 * (v / T) ≤ K * Y * (T ^ 2)⁻¹ := hlow.trans hmain
  have hl : 2 * T ^ 2 * (Y / 2 * (v / T)) = Y * (v * T) := by
    field_simp
  have hr : 2 * T ^ 2 * (K * Y * (T ^ 2)⁻¹) = Y * (2 * K) := by
    field_simp
  have h3 := mul_le_mul_of_nonneg_left hcomb (by positivity : (0 : ℝ) ≤ 2 * T ^ 2)
  rw [hl, hr] at h3
  have h4 : v * T ≤ 2 * K := le_of_mul_le_mul_left h3 hYpos
  have h5 : v * (2 * |K| / v) = 2 * |K| := by field_simp
  have h6 : v * T = v * (|C1| + |C2| + 4) + 2 * |K| := by
    rw [hT, mul_add, h5]
  have h7 : K ≤ |K| := le_abs_self K
  have h8 : 0 < v * (|C1| + |C2| + 4) := by positivity
  linarith

/-- The QUESTION of unit P1122-0105 settled: the LEAF `upper_slack_split_slack_distribution` of
SPLIT_upper_slack_split_rescaled_short_distribution, P0069 page 53 with display 5.17 on page 51,
stated here as the hypothesis `H` with its exact binders, implies that its cited inputs Theorem 4
and Lemma 9 are not both true. Instantiate it at the Buchstab model, eps = 10^-9,
delta = |P| + 1 and the constant rescalings lam = 1 and lam = 2, then apply the core above.
So the LEAF is false whenever its inputs hold, and vacuous otherwise. PROVED. -/
theorem upper_slack_split_slack_distribution_refuted
    (H : ∀ (_h4 : Thm4.Theorem4Paper) (_h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
      (_hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
      (_hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
      {ε : ℝ} (_hε : 0 < ε) (_hε8 : ε ≤ 1 / 10 ^ 8) {δ : ℝ} (_hδ : 0 < δ)
      {lam : ℝ → ℕ → ℝ} {Λ : ℝ} (_hb : ∀ x m, |lam x m| ≤ Λ)
      (_hX : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, 1 ≤ lam x m),
      Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε + δ) (upperNormCoeff ε lam)) :
    ¬ (Thm4.Theorem4Paper ∧ MeanValue132.Lemma9) := by
  rintro ⟨h4, h9⟩
  obtain ⟨ω, hω, hz⟩ := Task308.buchstab_model_exists
  have hε : (0 : ℝ) < 1 / 10 ^ 9 := by norm_num
  have hε8 : (1 : ℝ) / 10 ^ 9 ≤ 1 / 10 ^ 8 := by norm_num
  set P := ω (1/(1/4+(2*(1/16-1/10^5))/8-1/10^9)) / (1/4+(2*(1/16-1/10^5))/8-1/10^9) +
    upperDeletedIntegral ω (1 / 10 ^ 9) with hP
  have hδ : 0 < |P| + 1 := by positivity
  have hv : 0 < P + (|P| + 1) := by linarith [neg_abs_le P]
  have d1 := H h4 h9 hω hz hε hε8 hδ (lam := fun _ _ => 1) (Λ := 1)
    (fun _ _ => by norm_num) ⟨0, fun _ _ _ _ => le_rfl⟩
  have d2 := H h4 h9 hω hz hε hε8 hδ (lam := fun _ _ => 2) (Λ := 2)
    (fun _ _ => by norm_num) ⟨0, fun _ _ _ _ => by norm_num⟩
  exact upper_slack_short_distribution_two_scalings_absurd hε hε8 hv d1 d2

end LeanLab.BHP1997.DecompC165d

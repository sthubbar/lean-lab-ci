import LeanLab.ChenDoubleSieve.Decomp363d

/-!
Check the level condition and the logarithmic error order in Wu 2004.
Source: https://arxiv.org/pdf/0705.1652, page 6 equation 2.5 and page 38.
The squared logarithm obstruction is an elementary method check.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task363
open Task275 Task348

/-- For every fixed logarithmic loss the actual parameters eventually satisfy
z at least two and z squared at most Q, as required by Lemma 2.2. -/
theorem sieveLevel_eventually_admissible (B : ℝ) : ∃ N0 : ℕ,
    ∀ N : ℕ, N0 ≤ N → 2 ≤ (N : ℝ) ^ kappa1 ∧
      ((N : ℝ) ^ kappa1) ^ 2 ≤ sieveLevel B N := by
  have hs := (isLittleO_log_rpow_rpow_atTop B (s := (1 / 3 : ℝ)) (by norm_num)).bound
    (by norm_num : (0 : ℝ) < 1)
  have hsN := tendsto_natCast_atTop_atTop.eventually hs
  have hz : Tendsto (fun N : ℕ => (N : ℝ) ^ kappa1) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [kappa1])).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hsN.and (hz.eventually_ge_atTop 2))
  refine ⟨max 2 M, ?_⟩
  intro N hN
  obtain ⟨hsN, hzN⟩ := hM N (by omega)
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [Real.norm_of_nonneg (rpow_nonneg hlog.le _),
    Real.norm_of_nonneg (rpow_nonneg hpos.le _), one_mul] at hsN
  have he : ((N : ℝ) ^ kappa1) ^ 2 * (N : ℝ) ^ (1 / 3 : ℝ) =
      (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← rpow_two, ← rpow_mul hpos.le, ← rpow_add hpos]
    norm_num [kappa1]
  refine ⟨hzN, ?_⟩
  unfold sieveLevel
  apply (le_div_iff₀ (rpow_pos_of_pos hlog _)).2
  calc
    _ ≤ ((N : ℝ) ^ kappa1) ^ 2 * (N : ℝ) ^ (1 / 3 : ℝ) := by gcongr
    _ = _ := he


/-- Powers of two have no odd singular factor. -/
theorem CN_two_pow (k : ℕ) : CN (2 ^ k) = LeanLab.ChenExplicit.twinC := by
  unfold CN oddFactor
  cases k with
  | zero => simp
  | succ k => norm_num [Nat.primeFactors_pow_succ, Nat.prime_two.primeFactors, Finset.filter_singleton]

/-- An N over log squared error cannot be absorbed into every positive Theta budget.
The witness tail consists of powers of two. This is not a paper error claim. -/
theorem log_squared_not_absorbed : ¬ ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
    (N : ℝ) / log N ^ 2 ≤ (1 / (2 * LeanLab.ChenExplicit.twinC)) * Θ N := by
  rintro ⟨N0, hN0⟩
  let N : ℕ := 2 ^ (N0 + 1)
  have hN2 : 2 ≤ N := by
    dsimp [N]
    exact Nat.le_pow (by omega : 0 < N0 + 1)
  have hNge : N0 ≤ N := by
    have h := Nat.lt_two_pow_self (n := N0 + 1)
    dsimp [N]
    omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hscale : 0 < (N : ℝ) / log N ^ 2 := by positivity
  have hEven : Even N := ⟨2 ^ N0, by dsimp [N]; rw [pow_succ]; omega⟩
  have hbound := hN0 N hEven hNge
  have hcn : CN N = LeanLab.ChenExplicit.twinC := CN_two_pow _
  unfold Θ at hbound
  rw [hcn] at hbound
  have he : (1 / (2 * LeanLab.ChenExplicit.twinC)) *
      (LeanLab.ChenExplicit.twinC * N / log (N : ℝ) ^ 2) =
      ((N : ℝ) / log N ^ 2) / 2 := by
    field_simp [LeanLab.ChenExplicit.twinC_pos.ne']
  rw [he] at hbound
  linarith

end LeanLab.ChenDoubleSieve.Task363

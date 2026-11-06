import LeanLab.ChenDoubleSieve.Decomp366a
import LeanLab.ChenDoubleSieve.Decomp366d
import LeanLab.ChenDoubleSieve.Decomp363d

/-!
Finite admissibility for the F4 lower sieve application.
Source: https://arxiv.org/pdf/0705.1652, page 6 equation 2.5 and page 39 equation 10.5.
The pair product has a strict power margin before the sieve endpoint.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task366
open Task275 Task348

/-- The F4 pair product obeys the sharper fixed exponent bound. -/
theorem fullPairs4_product_sharp {N : ℕ} (hN : 2 ≤ N) {q : ℕ × ℕ}
    (hq : q ∈ fullPairs4 N) :
    ((q.1 * q.2 : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 * kappa2) := by
  obtain ⟨_, hp, hq, _, hlt, hqbound⟩ := mem_filter.mp hq
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpq : (q.1 : ℝ) ≤ q.2 := by exact_mod_cast hlt.le
  have hpbound : (q.1 : ℝ) ≤ (N : ℝ) ^ kappa2 := hpq.trans hqbound.le
  push_cast
  calc
    (q.1 : ℝ) * q.2 ≤ (N : ℝ) ^ kappa2 * (N : ℝ) ^ kappa2 :=
      mul_le_mul hpbound hqbound.le (by positivity) (by positivity)
    _ = (N : ℝ) ^ (kappa2 + kappa2) := (rpow_add hpos _ _).symm
    _ = _ := by congr 1; ring

/-- Every actual F4 residual level lies between three and six eventually.
This is strictly inside the lower sieve range and uses no function hypothesis. -/
theorem lowerLevel4_window (B : ℝ) (hB : 0 < B) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ q ∈ fullPairs4 N,
      lowerLevel B N (q.1 * q.2) ∈ Icc (3 : ℝ) 6 := by
  have he : ∀ᶠ N : ℕ in atTop, 3 + 24 * kappa2 < lowerLevel B N 1 :=
    (lowerLevel_one_tendsto B).eventually
      (eventually_gt_nhds (by norm_num [kappa2]))
  obtain ⟨M, hM⟩ := eventually_atTop.1 he
  obtain ⟨J, hJ⟩ := lowerLevel_window B hB
  refine ⟨max 2 (max M J), ?_⟩
  intro N hN q hq
  have hN2 : 2 ≤ N := by omega
  obtain ⟨hd, hwide⟩ := fullPairs4_product hN2 hq
  have hsharp := fullPairs4_product_sharp hN2 hq
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hdpos : (0 : ℝ) < (q.1 * q.2 : ℕ) := by exact_mod_cast (show 0 < q.1 * q.2 by omega)
  have hdl : log ((q.1 * q.2 : ℕ) : ℝ) ≤ (2 * kappa2) * log N := by
    have hh := log_le_log hdpos hsharp
    rwa [log_rpow hpos] at hh
  have hcorr : 12 * log ((q.1 * q.2 : ℕ) : ℝ) / log N ≤ 24 * kappa2 :=
    (div_le_iff₀ hlog).2 (by nlinarith)
  have hbase := hM N (by omega)
  have hupper := (hJ N (by omega) _ hd hwide).2
  refine ⟨?_, hupper⟩
  rw [lowerLevel_divisor B hN2 hd]
  linarith

/-- The actual pair residual sieve level eventually exceeds the square of z
uniformly over the full F4 domain. -/
theorem pair_sieveLevel_admissible (B : ℝ) : ∃ N0 : ℕ,
    ∀ N : ℕ, N0 ≤ N → ∀ q ∈ fullPairs4 N,
      2 ≤ (N : ℝ) ^ kappa1 ∧
        ((N : ℝ) ^ kappa1) ^ 2 ≤ Task363.sieveLevel B N / (q.1 * q.2 : ℕ) := by
  let r : ℝ := 1 / 2 - 2 * kappa1 - 2 * kappa2
  have hr : 0 < r := by norm_num [r, kappa1, kappa2]
  have hs := (isLittleO_log_rpow_rpow_atTop B (s := r) hr).bound
    (by norm_num : (0 : ℝ) < 1)
  have hz : Tendsto (fun N : ℕ => (N : ℝ) ^ kappa1) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [kappa1])).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.1
    ((tendsto_natCast_atTop_atTop.eventually hs).and (hz.eventually_ge_atTop 2))
  refine ⟨max 2 M, ?_⟩
  intro N hN q hq
  obtain ⟨hsN, hzN⟩ := hM N (by omega)
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [Real.norm_of_nonneg (rpow_nonneg hlog.le _),
    Real.norm_of_nonneg (rpow_nonneg hpos.le _), one_mul] at hsN
  have hd := (fullPairs4_product (by omega) hq).1
  have hdpos : (0 : ℝ) < (q.1 * q.2 : ℕ) := by exact_mod_cast (show 0 < q.1 * q.2 by omega)
  have hsharp := fullPairs4_product_sharp (by omega) hq
  have hid : ((N : ℝ) ^ kappa1) ^ 2 * (N : ℝ) ^ (2 * kappa2) * (N : ℝ) ^ r =
      (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← rpow_two, ← rpow_mul hpos.le, ← rpow_add hpos, ← rpow_add hpos]
    congr 1
    dsimp [r]
    ring
  refine ⟨hzN, ?_⟩
  apply (le_div_iff₀ hdpos).2
  unfold Task363.sieveLevel
  apply (le_div_iff₀ (rpow_pos_of_pos hlog _)).2
  calc
    _ ≤ ((N : ℝ) ^ kappa1) ^ 2 * (N : ℝ) ^ (2 * kappa2) * (N : ℝ) ^ r := by
      gcongr
    _ = _ := hid

/-- Every actual pair discrepancy is the stated arithmetic progression discrepancy. -/
theorem rawRemainder4_AP (B : ℝ) (N : ℕ) :
    rawRemainder4 B N = ∑ p ∈ lowerPairs4 N, ∑ q ∈ pairModuli4 B N p,
      |(#((range (N + 1)).filter (fun r => r.Prime ∧ r ≡ N [MOD p.1 * p.2 * q])) : ℝ) -
        Wu04.li N / (Nat.totient (p.1 * p.2 * q) : ℝ)| := by
  unfold rawRemainder4
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q hq
  rw [Task363.primeSequence_divisor_card]
  have he : (range (N + 1)).filter
      (fun r => r.Prime ∧ r % (p.1 * p.2 * q) = N % (p.1 * p.2 * q)) =
      (range (N + 1)).filter (fun r => r.Prime ∧ r ≡ N [MOD p.1 * p.2 * q]) := by
    apply Finset.filter_congr
    intro r hr
    rfl
  rw [he]

/-- Residual modulus one is present whenever the residual level reaches one. -/
theorem one_mem_pairModuli4 {B : ℝ} {N : ℕ} {p : ℕ × ℕ}
    (hQ : 1 ≤ Task363.sieveLevel B N / (p.1 * p.2 : ℕ)) :
    1 ∈ pairModuli4 B N p := by
  apply mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨le_refl _, Nat.le_floor (by simpa using hQ)⟩, squarefree_one, ?_⟩
  exact Nat.coprime_one_left _

/-- The concrete nonempty pair instance also has a residual discrepancy modulus. -/
theorem pairModuli4_instance : 1 ∈ pairModuli4 1 68719476736 (11, 13) := by
  apply one_mem_pairModuli4
  have hsqrt : ((68719476736 : ℕ) : ℝ) ^ (1 / 2 : ℝ) = 262144 := by
    have he (r : ℝ) : ((68719476736 : ℕ) : ℝ) ^ r = (2 : ℝ) ^ (36 * r) := by
      rw [rpow_mul (by norm_num)]
      norm_num
    rw [he]
    norm_num
  have hlog0 : 0 < log (((68719476736 : ℕ) : ℝ)) := log_pos (by norm_num)
  have hlog : log (((68719476736 : ℕ) : ℝ)) ≤ 36 := by
    have he : ((68719476736 : ℕ) : ℝ) = (2 : ℝ) ^ (36 : ℕ) := by norm_num
    rw [he, log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp only [Task363.sieveLevel, hsqrt, rpow_one]
  norm_num only [Nat.cast_ofNat, Nat.cast_mul, mul_one]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 143)).2
  apply (le_div_iff₀ hlog0).2
  nlinarith

end LeanLab.ChenDoubleSieve.Task366

import LeanLab.ChenDoubleSieve.Decomp349n

/-!
The reduced common factor sum in Wu 2004 page 40 before equation 10.8.
Source: https://arxiv.org/pdf/0705.1652.
This bounds the reduced majorant alone. The switched progression estimate is separate.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348

/-- The reduced squarefree common factor majorant with an inclusive lower cutoff. -/
def commonFactorMajorant (σ : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) * ∑ d ∈ (Finset.range (N + 1)).filter
      (fun d : ℕ => Squarefree d ∧ (N : ℝ) ^ σ ≤ (d : ℝ)),
    (1 / ((d : ℝ) * d.totient)) *
      ∑ l ∈ (Finset.range (Nat.sqrt N / d + 1)).filter Squarefree,
        1 / (l.totient : ℝ)

/-- The reduced common factor sum has the printed power saving and two logarithms. -/
theorem commonFactorMajorant_bound : ∃ C : ℝ, 0 < C ∧
    ∀ σ : ℝ, ∀ N : ℕ, 2 ≤ N →
      commonFactorMajorant σ N ≤ C * (N : ℝ) ^ (1 - σ) * log N ^ 2 := by
  obtain ⟨K, hK, hmass⟩ := squarefree_totient_sum_log_bounded
  refine ⟨4 * K ^ 2, by positivity, ?_⟩
  intro σ N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow : 0 < (N : ℝ) ^ σ := rpow_pos_of_pos hn _
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlog' : 0 ≤ log ((N : ℝ) + 1) := log_nonneg (by have := hn.le; linarith)
  have hinner (d : ℕ) :
      (∑ l ∈ (Finset.range (Nat.sqrt N / d + 1)).filter Squarefree,
        1 / (l.totient : ℝ)) ≤ K * log ((N : ℝ) + 1) := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (hmass N hN)
    · apply Finset.filter_subset_filter
      apply Finset.range_mono
      exact Nat.add_le_add_right ((Nat.div_le_self _ _).trans (Nat.sqrt_le_self N)) 1
    · intros
      positivity
  have houter :
      (∑ d ∈ (Finset.range (N + 1)).filter
          (fun d : ℕ => Squarefree d ∧ (N : ℝ) ^ σ ≤ (d : ℝ)),
        1 / (d.totient : ℝ)) ≤ K * log ((N : ℝ) + 1) := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (hmass N hN)
    · intro d hd
      obtain ⟨hdr, hds, _⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_filter.mpr ⟨hdr, hds⟩
    · intros
      positivity
  have hsum : commonFactorMajorant σ N ≤
      K ^ 2 * (N : ℝ) ^ (1 - σ) * log ((N : ℝ) + 1) ^ 2 := by
    unfold commonFactorMajorant
    calc
      _ ≤ (N : ℝ) * ∑ d ∈ (Finset.range (N + 1)).filter
          (fun d : ℕ => Squarefree d ∧ (N : ℝ) ^ σ ≤ (d : ℝ)),
            (K * log ((N : ℝ) + 1) / (N : ℝ) ^ σ) * (1 / (d.totient : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hn.le
        apply Finset.sum_le_sum
        intro d hd
        have hcut := (Finset.mem_filter.mp hd).2.2
        have hdpos : (0 : ℝ) < d := hpow.trans_le hcut
        have hrec : 1 / (d : ℝ) ≤ 1 / (N : ℝ) ^ σ :=
          one_div_le_one_div_of_le hpow hcut
        calc
          _ ≤ (1 / ((d : ℝ) * d.totient)) * (K * log ((N : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left (hinner d) (by positivity)
          _ = (1 / (d : ℝ)) * (1 / (d.totient : ℝ)) * (K * log ((N : ℝ) + 1)) := by ring
          _ ≤ (1 / (N : ℝ) ^ σ) * (1 / (d.totient : ℝ)) * (K * log ((N : ℝ) + 1)) := by
            gcongr
          _ = _ := by ring
      _ = (N : ℝ) * ((K * log ((N : ℝ) + 1) / (N : ℝ) ^ σ) *
          ∑ d ∈ (Finset.range (N + 1)).filter
            (fun d : ℕ => Squarefree d ∧ (N : ℝ) ^ σ ≤ (d : ℝ)), 1 / (d.totient : ℝ)) := by
        congr 1
        rw [Finset.mul_sum]
      _ ≤ (N : ℝ) * ((K * log ((N : ℝ) + 1) / (N : ℝ) ^ σ) *
          (K * log ((N : ℝ) + 1))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left houter (by positivity)) hn.le
      _ = _ := by rw [rpow_sub hn, rpow_one]; ring
  have hlogbound : log ((N : ℝ) + 1) ≤ 2 * log N := by
    have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    calc
      _ ≤ log ((N : ℝ) ^ 2) := log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [log_pow]; norm_num
  have hlogsq : log ((N : ℝ) + 1) ^ 2 ≤ 4 * log N ^ 2 := by nlinarith
  calc
    _ ≤ K ^ 2 * (N : ℝ) ^ (1 - σ) * log ((N : ℝ) + 1) ^ 2 := hsum
    _ ≤ K ^ 2 * (N : ℝ) ^ (1 - σ) * (4 * log N ^ 2) := by gcongr
    _ = _ := by ring

/-- The reduced common factor majorant fits every positive Theta budget. -/
theorem commonFactorMajorant_absorbed {σ : ℝ} (hσ : 0 < σ)
    (ε : ℝ) (hε : 0 < ε) : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      commonFactorMajorant σ N ≤ ε * Θ N := by
  obtain ⟨C, hC, hbound⟩ := commonFactorMajorant_bound
  obtain ⟨M, hM⟩ := log_weighted_power_absorbed hσ 2 C ε hC.le hε
  exact ⟨max 2 M, fun N hN => (hbound σ N (by omega)).trans (hM N (by omega))⟩

end LeanLab.ChenDoubleSieve.Task349

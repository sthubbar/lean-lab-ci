/- AI wrote the Lean code for CODEX task333. Goldbach is open.
Direct non-strict sieve specialization at the original level.
Journal p. 1229, first display in the proof of Theorem 5. -/
import LeanLab.BS2022GRH.DecompC169a

namespace LeanLab.BS2022GRH.WeakSieve333
open Real Finset Classical ChenThresholdGRH DecompC169a
noncomputable section

/-- Apply the supplied sieve at z itself, with the band estimate only there.
No nearby level or strict coefficient gain is required.
Journal p. 1229. CONDITIONAL ON LinearSieveT4 and the fixed level band estimate. -/
theorem lower_sieve_fixed_level (α u ε C₁ C₂ : ℝ) (n : ℕ)
    (hT : LinearSieveT4 ε C₁ C₂) (heps : epsJ u ≤ ε)
    (he0 : 0 < ε) (he1 : ε < 1 / 63) (hα : 0 < α) (hα1 : α < 1 / 8)
    (hu : 400 ≤ u) (hnlog : 3200 < log (n : ℝ)) (hev : Even n)
    (hband : ∀ v, u ≤ v → v < U7153.zz n →
      (∏ p ∈ (range ⌈U7153.zz n⌉₊).filter
        (fun p : ℕ => p.Prime ∧ v ≤ (p : ℝ) ∧ (p : ℝ) < U7153.zz n),
        (1 - 1 / ((p : ℝ) - 1))⁻¹) <
          (1 + epsJ u) * (log (U7153.zz n) / log v)) :
    sieveMain n α ε C₂ - remainder n α u ≤ (U7153.SA n : ℝ) := by
  have hn1 : (1 : ℝ) < n := (log_pos_iff (Nat.cast_nonneg n)).mp (by linarith)
  have hn0 : (0 : ℝ) < n := by linarith
  let z := U7153.zz n
  let D := (n : ℝ) ^ (1 / 2 - α)
  have hz0 : 0 < z := rpow_pos_of_pos hn0 _
  have hD0 : 0 < D := rpow_pos_of_pos hn0 _
  have hlz : log z = (1 / 8 : ℝ) * log (n : ℝ) := log_rpow hn0 _
  have hlD : log D = (1 / 2 - α) * log (n : ℝ) := log_rpow hn0 _
  have hlz400 : 400 < log z := by rw [hlz]; linarith
  have hz1 : 1 < z := (log_pos_iff hz0.le).mp (by linarith)
  have hz2 : 2 ≤ z := by
    have h := log_le_sub_one_of_pos hz0
    linarith
  have hs : log D / log z = 4 - 8 * α := by
    rw [hlD, hlz]
    field_simp
    <;> ring
  have hzD : z ^ 2 ≤ D := by
    apply (log_le_log_iff (pow_pos hz0 2) hD0).mp
    rw [log_pow, hlz, hlD]
    norm_num
    nlinarith
  have hprod := lower_product_guard n u ε z hu hz1 he0.le heps hband
  have hg : ∀ x : ℕ, ∀ p ∈ ({p : ℕ | p.Prime ∧ ¬ p ∣ n} : Set ℕ),
      0 ≤ 1 / ((p : ℝ) - 1) ∧ 1 / ((p : ℝ) - 1) < 1 := by
    intro x p hp
    have hp3 : 3 ≤ p := by
      have hp2 := hp.1.two_le
      have hne : p ≠ 2 := fun h => hp.2 (h ▸ hev.two_dvd)
      omega
    have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    exact ⟨div_nonneg (by norm_num) (by linarith),
      (div_lt_one (by linarith)).mpr (by linarith)⟩
  have hQ : (↑(primesBelow n u) : Set ℕ) ⊆ {p : ℕ | p.Prime ∧ ¬ p ∣ n} := by
    intro p hp
    exact ⟨(mem_filter.mp hp).2.1, (mem_filter.mp hp).2.2.1⟩
  have key := hT (U7153.Aset n) (fun m => if m ∈ U7153.Aset n then (1 : ℝ) else 0)
    {p : ℕ | p.Prime ∧ ¬ p ∣ n} (primesBelow n u) (fun _ p => 1 / ((p : ℝ) - 1)) z D
    (by intro m; split_ifs <;> norm_num) (by intro m hm; simp [hm])
    (fun _ hp => hp.1) hQ hg he0 he1 hz2 (fun _ v hv hvz => by
      convert hprod v hv hvz using 1 <;> congr 1 <;> ext p <;> simp)
  have hmain := key.2 hzD (by rw [hs]; linarith)
  simp only [filter_congr_decidable] at hmain
  rw [lower_prime_set n z, lower_sifted_sum n, lower_main_mass n,
    lower_remainder_sum n α u, hs, lower_coefficient_at_parameter α ε C₂ hα1] at hmain
  simpa only [sieveMain, mul_assoc] using hmain

end
end LeanLab.BS2022GRH.WeakSieve333

#print axioms LeanLab.BS2022GRH.WeakSieve333.lower_sieve_fixed_level

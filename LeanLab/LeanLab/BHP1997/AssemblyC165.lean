/-
P0069, Theorem 1, pages 1 to 4. The existing finite deduction now
uses the new explicit decomposition of sieve_data.
CONDITIONAL on all OPEN analytic leaves in DecompC165a, b and c.
AI wrote the Lean code. CODEX task165. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165b

namespace LeanLab.BHP1997.AssemblyC165
open Classical Real Filter Decomp132

/-- Pages 1 to 4, the exact Theorem1 Prop follows from the new
sieve_data decomposition and the already proved finite sandwich and
covering lemmas. No direct sorry. CONDITIONAL on the named leaves. -/
theorem theorem1 : Theorem1 := by
  obtain ⟨ε, u0, u1, v0, v1, hε, hε1, hu0, hu, hu1, hv0, hv, hv1, hdata⟩ := DecompC165b.sieve_data
  have hm := constants15 hu0 hu hu1 hv0 hv hv1
  have hδ := theta12 hε hε1
  intro θ hθ
  apply cover_short_intervals (by linarith : 0 < (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))
    (by linarith : (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) < 1)
    (lt_of_lt_of_le hδ.1 hθ)
  intro A hA
  obtain ⟨C, hC⟩ := hdata A hA
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨I, J, a0, a1, b0, b1, E, ha, hb, hE, hcorr⟩ := hC x hx
  have hsub : (Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
      (fun N => Even N ∧ ¬ IsGoldbachSum N) ⊆ E := by
    intro N hN
    obtain ⟨hNI, hEven, hnot⟩ := Finset.mem_filter.mp hN
    by_contra hNE
    obtain ⟨r, hr, h01, h10, h11⟩ := hcorr N hNI hEven hNE
    have hpos := correlation_positive hm hr h01 h10 h11
    have hle := convolution_sandwich ha hb N
    rw [prime_convolution_zero I J hnot] at hle
    linarith
  exact lt_of_le_of_lt (by exact_mod_cast Finset.card_le_card hsub) hE

end LeanLab.BHP1997.AssemblyC165

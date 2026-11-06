/-
P0079 positive-margin and existential-threshold assembly with three analytic inputs.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp418a
import LeanLab.LZPowersOfTwo.Decomp418b
import LeanLab.LZPowersOfTwo.Decomp353a
import LeanLab.LZPowersOfTwo.MinorAssembly396
import LeanLab.LZPowersOfTwo.Decomp293d

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 pages 4 to 5, displays 13 to 19. CONDITIONAL ON prime_integer_l2_small418,
paired_second_moment396 and minor_bad353. Counting and the trivial arc
are proved inputs. The exact positive-margin counting conclusion is preserved. -/
theorem count_bound_at_margin418 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : (ν = nuTr ∧ IsTr (l1 / l2)) ∨ (ν = nuAlg ∧ IsAlg (l1 / l2)))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l1))
    (hM : 0 < ∑ i : Fin s, |μ i|)
    (hgap : 0 < (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η - ν ^ (s - 2) * Cq r1.den r2.den) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
      c * X * (cutoff293 s μ ε X) ^ s ≤
        η * (log X) ^ 2 * NX l1 l2 (fun i : Fin s => μ i) γ η ε X := by
  let gap := (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η - ν ^ (s - 2) * Cq r1.den r2.den
  have hg : 0 < gap := hgap
  have hε1 : ε < 1 := by
    have hd : 1 / (8 * l1) < (1 : ℝ) := (div_lt_one (by positivity)).mpr (by linarith)
    exact hε'.trans hd
  have Hmajor := major_lower418 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
  have Hminor := minor_upper396 ν s l1 l2 μ γ η ε hs h1 h2 hr hi hc hμ r1 r2
    hr1 hr2 hη hη1 hη2 hε hε' (gap / 4) (by positivity)
  have Htrivial := trivial_small418 s l1 l2 μ γ η ε hs (by linarith) (by linarith)
    hμ hη hε hε1 (gap * η / 4) (by positivity)
  refine ⟨gap * η / 2, by positivity, ?_⟩
  filter_upwards [Hmajor, Hminor, Htrivial, eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop ((2 * ∑ i : Fin s, |μ i|) / ε)] with X hmajor hminor htrivial hX hXM
  obtain ⟨hint, hcount⟩ := count_integral353 s l1 l2 μ γ η ε X hη hε hX
  have hL : 0 ≤ cutoff293 s μ ε X := cutoff_nonneg293 s μ ε X hM
    (by simpa [mul_comm] using (div_le_iff₀ hε).mp hXM)
  have hW : 0 ≤ X * (cutoff293 s μ ε X) ^ s := mul_nonneg (by linarith) (pow_nonneg hL _)
  have hbound := arc_lower293 (integrand293 s l1 l2 μ γ η ε X) hint X
    (cutoff293 s μ ε X)
    ((1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2)
    ((ν ^ (s - 2) * Cq r1.den r2.den + gap / 4) * η)
    (gap * η / 4) (X * (cutoff293 s μ ε X) ^ s)
    (by nlinarith only [hmajor]) (by nlinarith only [hminor]) (by nlinarith only [htrivial])
  have heq : ((1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 -
      (ν ^ (s - 2) * Cq r1.den r2.den + gap / 4) * η - gap * η / 4) = gap * η / 2 := by
    dsimp [gap]
    ring
  rw [heq] at hbound
  nlinarith only [hbound, hcount]

/-- P0079 page 4, display 13 and its consequence. CONDITIONAL ON the three remaining
major and minor leaves. This is the quantitative conclusion at a fixed strict margin.
It does not infer that margin from the sealed s0 formula. -/
theorem density_at_margin418 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : (ν = nuTr ∧ IsTr (l1 / l2)) ∨ (ν = nuAlg ∧ IsAlg (l1 / l2)))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l1))
    (hM : 0 < ∑ i : Fin s, |μ i|)
    (hgap : 0 < (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η - ν ^ (s - 2) * Cq r1.den r2.den) :
    ∃ c X0 : ℝ, 0 < c ∧ ∀ X, X0 ≤ X →
      c * X * (log X) ^ (s - 2) ≤ NX l1 l2 (fun i : Fin s => μ i) γ η ε X := by
  obtain ⟨c, hc', H⟩ := count_bound_at_margin418 ν s l1 l2 μ γ η ε hs h1 h2 hr hi hc hμ
    r1 r2 hr1 hr2 hη hη1 hη2 hε hε' hM hgap
  exact count_to_density293 s l1 l2 μ γ η ε c hs hM hη hε hc' H


/-- P0079 pages 3 to 5, the strict-margin existential-threshold argument.
CONDITIONAL ON prime_integer_l2_small418, paired_second_moment396 and minor_bad353.
This is the exact normalized_large_s293 statement and does not assert the printed s0 endpoint. -/
theorem normalized_large_s418 (ν l1 l2 : ℝ) (μ : ℕ → ℝ)
    (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : (ν = nuTr ∧ IsTr (l1 / l2)) ∨ (ν = nuAlg ∧ IsAlg (l1 / l2)))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (η : ℝ) (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|) :
    ∃ S0 : ℕ, ∀ s : ℕ, 2 ≤ s → S0 ≤ s → ∀ γ : ℝ,
      (Sol l1 l2 (fun i : Fin s => μ i) γ η).Infinite := by
  have hν0 : 0 ≤ ν := by
    rcases hc with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact nuTr_pos.le
    · exact nuAlg_pos.le
  have hν1 : ν < 1 := by
    rcases hc with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact nuTr_lt_one
    · exact nuAlg_lt_one
  have hprod : 0 < |l1 * l2| := abs_pos.mpr (mul_ne_zero (by linarith) (by linarith))
  have hlim := ((tendsto_pow_atTop_nhds_zero_of_lt_one hν0 hν1).comp
    (tendsto_sub_atTop_nat 2)).mul_const (Cq r1.den r2.den)
  have Hpow : ∀ᶠ s : ℕ in atTop,
      ν ^ (s - 2) * Cq r1.den r2.den < η / (8 * |l1 * l2|) :=
    hlim.eventually (eventually_lt_nhds (by simpa using (div_pos hη
      (show 0 < 8 * |l1 * l2| by positivity))))
  obtain ⟨S0, hS0⟩ := eventually_atTop.mp Hpow
  refine ⟨S0, fun s hs hS γ => ?_⟩
  let ε : ℝ := 1 / (16 * l1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε' : ε < 1 / (8 * l1) := by
    dsimp [ε]
    apply one_div_lt_one_div_of_lt (by positivity)
    linarith
  have hgap : 0 < (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η -
      ν ^ (s - 2) * Cq r1.den r2.den := by
    have heq : (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η =
        3 * η / (8 * |l1 * l2|) := by
      dsimp [ε]
      field_simp
      ring
    rw [heq, show 3 * η / (8 * |l1 * l2|) = 3 * (η / (8 * |l1 * l2|)) by ring]
    have hb := hS0 s hS
    have hp : 0 < η / (8 * |l1 * l2|) := by positivity
    linarith
  have hmass : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  exact infinite_of_NX_lower293 (density_at_margin418 ν s l1 l2 μ γ η ε hs h1 h2 hr hi hc
    hμ r1 r2 hr1 hr2 hη hη1 hη2 hε hε' hmass hgap)



end LeanLab.LZPowersOfTwo

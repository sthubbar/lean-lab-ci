import LeanLab.ChenDoubleSieve.Decomp363f

/-!
Supply split for the ordinary upper bounds in Wu 2004.
Source: https://arxiv.org/pdf/0705.1652, page 39 equations 10.3 and 10.4.
The finite main terms retain the logarithmic sieve level loss.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- The upper endpoint for the prime band of each ordinary coordinate. -/
def basicEndpoint (i : Fin 12) : ℝ :=
  if i = 1 then kappa2 else if i = 2 then sigma1 else sigma2

/-- The sifting level is p in coordinate one and N to kappa one otherwise. -/
def basicSifting (N p : ℕ) (i : Fin 12) : ℝ :=
  if i = 1 then p else (N : ℝ) ^ kappa1

/-- The finite main term before replacing the prime sum by an integral.
The residual Q divided by p retains Q equal square root N over log N to B. -/
def basicMain (F : ℝ → ℝ) (B : ℝ) (N : ℕ) (i : Fin 12) : ℝ :=
  (N : ℝ) / log N * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1)
      ((N : ℝ) ^ basicEndpoint i),
    Task363.localDensity N (basicSifting N p i) / ((p : ℝ) - 1) *
      F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / p) /
        log (basicSifting N p i))

/-- LEAF. Wu 2004 page 39, display before 10.3 and the same sieve step for 10.4.
Only the count to finite prime sum comparison is asserted.
The passage from li N to N over log N is included in the error. -/
theorem basic_finite_upper (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        ∀ i : Fin 12, i ∈ ({1, 2, 3} : Finset (Fin 12)) →
          sieveTerms N i ≤ basicMain F B N i + η * Θ N := by
  sorry

/-- LEAF. Wu 2004 page 39, replacement of the prime sums in 10.3 and 10.4.
This has no actual sieve count. It includes product normalization,
prime partial summation and removal of the finite logarithmic level loss. -/
theorem basic_main_tendsto (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) :
    ∀ i : Fin 12, i ∈ ({1, 2, 3} : Finset (Fin 12)) →
      Tendsto (fun N => basicMain F B N i / Θ N) evenAtTop
        (𝓝 (integralTerms F f ω i)) := by
  sorry

/-- An upper count estimate follows from a finite main term and its limit.
This is the elementary final normalization used on pages 39 to 41. -/
theorem upper_of_main (c : ℝ) (u : ℕ → ℝ) (main : ℝ → ℕ → ℝ)
    (hsieve : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N → u N ≤ main B N + η * Θ N)
    (hlimit : ∀ B : ℝ, 0 < B →
      Tendsto (fun N => main B N / Θ N) evenAtTop (𝓝 c)) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      u N ≤ (c + ε) * Θ N := by
  intro ε hε
  obtain ⟨B, hB, M, hM⟩ := hsieve (ε / 2) (by positivity)
  have he : ∀ᶠ N in evenAtTop, main B N / Θ N < c + ε / 2 :=
    (hlimit B hB).eventually (eventually_lt_nhds (by linarith : c < c + ε / 2))
  obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_inf_principal.1 he)
  refine ⟨max 2 (max M K), ?_⟩
  intro N hEven hN
  have ht := Θ_pos (show 2 ≤ N by omega)
  have hc := (div_lt_iff₀ ht).1 (hK N (by omega) hEven)
  have hs := hM N hEven (by omega)
  nlinarith

/-- Finitely many separate thresholds give one threshold for the whole group. -/
theorem finite_upper_threshold (I : Finset (Fin 12)) (u : ℕ → Fin 12 → ℝ)
    (c : Fin 12 → ℝ)
    (h : ∀ i ∈ I, ∀ ε : ℝ, 0 < ε → ∃ M : ℕ,
      ∀ N : ℕ, Even N → M ≤ N → u N i ≤ (c i + ε) * Θ N) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ N : ℕ, Even N → M ≤ N →
      ∀ i ∈ I, u N i ≤ (c i + ε) * Θ N := by
  intro ε hε
  have he : ∀ i ∈ I, ∀ᶠ N in evenAtTop, u N i ≤ (c i + ε) * Θ N := by
    intro i hi
    obtain ⟨M, hM⟩ := h i hi ε hε
    exact eventually_inf_principal.2 (eventually_atTop.2
      ⟨M, fun N hN hEven => hM N hEven hN⟩)
  have hall := I.eventually_all.2 he
  obtain ⟨M, hM⟩ := eventually_atTop.1 (eventually_inf_principal.1 hall)
  exact ⟨M, fun N hEven hN => hM N hN hEven⟩

/-- The exact sealed basic_upper conclusion from two strictly smaller leaves.
OPEN through basic_finite_upper and basic_main_tendsto. -/
theorem basic_upper_supplied (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({1, 2, 3} : Finset (Fin 12)) →
        sieveTerms N i ≤ (integralTerms F f ω i + ε) * Θ N := by
  apply finite_upper_threshold
  intro i hi
  apply upper_of_main _ _ (fun B N => basicMain F B N i)
  · intro η hη
    obtain ⟨B, hB, M, hM⟩ := basic_finite_upper F f h η hη
    exact ⟨B, hB, M, fun N hEven hN => hM N hEven hN i hi⟩
  · exact fun B hB => basic_main_tendsto F f ω h B hB i hi

end LeanLab.ChenDoubleSieve.Task349

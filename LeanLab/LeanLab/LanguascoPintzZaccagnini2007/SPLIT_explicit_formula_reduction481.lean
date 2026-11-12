import LeanLab.LanguascoPintzZaccagnini2007.Decomp481c

/-!
The split of `explicit_formula_reduction481`: the reduction of the explicit formula on
pages 5 and 6 of the source paper to a finite zero sum, together with the counting and
uniform bounds that the reduction consumes.

The open leaves are
* `zero_family_card_bound481`, the size of the indexed zero family, from the zero density
  input and the occurrence bound;
* `singular_series_lower481`, the uniform positive lower bound for the singular series on
  the even window;
* `absorption_constants481`, the choice of the height `H`, the frequency cut-off `T` and the
  small parameter, together with the two arithmetic inequalities they must satisfy;
* `explicit_formula_main_term481` and `explicit_formula_total_size481`, the near diagonal and
  the crude size of the finite zero sum of Lemma 4.1 for one integer `n`.

`explicit_formula_reduction481_split` is the assembly: the same statement as the target,
derived from the leaves, with no open step of its own.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real
open scoped Classical

noncomputable section

/-! ### A threshold helper for the assembly

`log X` eventually dominates any fixed height, so every zero of the box eventually sits in the
closed strip `1/2 ≤ re ≤ 1`; this is the only place where the height enters the strip. -/

private theorem log_threshold481 (H : ℝ) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → 2 * H ≤ Real.log X := by
  have h : Filter.Tendsto (fun X : ℕ => Real.log X) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact Filter.eventually_atTop.mp (h.eventually (Filter.eventually_ge_atTop (2 * H)))

/-! ### The leaves -/

/-- LEAF. Page 5, the density estimate following display 8: the size of the zero family.
The family of Lemma 4.1 lists its zeros with multiplicity, so the number `K` of non-pole
members is at most the total analytic multiplicity of the listed zeros, and the density input
bounds that total in terms of the height alone. This is the counting step only: it asserts
nothing about the major arcs or about the singular series. -/
theorem zero_family_card_bound481 (hdensity : JutilaStatement481)
    (hcount : ∀ {K : ℕ} (z : Fin K → Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
      (∀ w, (univ.filter (fun i => z i = w)).card ≤
        analyticOrderNatAt (Lfun481 w.2.1) w.2.2) →
      (K : ℝ) ≤ ∑ w ∈ univ.image z, (analyticOrderNatAt (Lfun481 w.2.1) w.2.2 : ℝ)) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ H T : ℝ, 1 ≤ H → 1 ≤ T → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ P : ℝ, AdmissibleP131 X P →
      ∀ (K : ℕ) (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
        (z 0).1 = 1 → (z 0).2.2 = 1 → (∀ i, i ≠ 0 → z i ∈ zeroBox481 X H T P) →
        (∀ w, (univ.filter (fun i => i ≠ 0 ∧ z i = w)).card ≤
          analyticOrderNatAt (Lfun481 w.2.1) w.2.2) →
        (K : ℝ) ≤ C₀ * Real.exp (4 * H) := by
  sorry

/-- LEAF. Page 2, display 2: for even `n` the singular series is `2 c_0` times a product of
factors `(p - 1) / (p - 2)` over odd primes `p` dividing `n`, each at least one, so it is at least
the twin prime constant `2 c_0`, which is positive. Every member of the even window is even, so
this gives a uniform positive lower bound there. The page 6 paragraph before Corollary 4.2 states
no lower bound for the singular series; the earlier citation of that paragraph was wrong and is
corrected by architect U-1649. Only positivity, not any asymptotic, is used by the reduction. -/
theorem singular_series_lower481 :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ (X n : ℕ), n ∈ evenJ131 X → s₀ ≤ Sing n := by
  sorry

/-- LEAF. Page 6, the choice of the parameters: the height and the frequency cut-off can be
taken large enough that the uniform remainder of Lemma 4.1 is below `η s₀ / 2`, and then the
small parameter can be taken small enough that the off-diagonal contribution is below
`η s₀ / 2` as well. This is a real-variable existence statement with no number theory in it:
`exp (-c H)` and `T ^ (-1/2)` are made small, and then the factor
`(C₀ exp (4 H) + 2) ^ 2 π` is compensated by `ε`. -/
theorem absorption_constants481 (c B ε₀ s₀ C₀ η H₀ T₀ : ℝ)
    (hc : 0 < c) (hB : 0 ≤ B) (hε₀ : 0 < ε₀) (hs₀ : 0 < s₀) (hC₀ : 0 ≤ C₀)
    (hη : 0 < η) :
    ∃ H T ε : ℝ, H₀ ≤ H ∧ 1 ≤ H ∧ T₀ ≤ T ∧ 1 ≤ T ∧ 0 < ε ∧ ε < ε₀ ∧
      2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T) ≤ η * s₀ / 2 ∧
      (C₀ * Real.exp (4 * H) + 2) ^ 2 * Real.pi * ε ≤ η * s₀ / 2 := by
  sorry

/-- LEAF. Page 5, Lemma 4.1: the finite zero sum for one integer `n`. The pole pair carries
the full main term `n * Sing n`, and every pair with at least one zero factor contributes at
most the small parameter. This is a single sum estimate: it has no exceptional set, no
counting and no uniformity in `X`. -/
theorem explicit_formula_main_term481 {K : ℕ}
    (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
    (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ) (n : ℕ) (ε : ℝ)
    (hz0 : (z 0).2.2 = 1) (hSg00 : Sg 0 0 n = (Sing n : ℂ))
    (hγ : ∀ i j, ‖gammaPair481 (z i).2.2 (z j).2.2 n‖ ≤ Real.pi * n)
    (hε : 0 ≤ ε) (hSgε : ∀ i j, (i ≠ 0 ∨ j ≠ 0) → ‖Sg i j n‖ ≤ ε) :
    |(∑ i, ∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
        gammaPair481 (z i).2.2 (z j).2.2 n).re - n * Sing n| ≤
      ((K : ℝ) + 1) ^ 2 * ε * Real.pi * n := by
  sorry

/-- LEAF. Page 5, Lemma 4.1: the crude size of the same finite zero sum for one integer `n`,
with every pair counted at its uniform bound `Sing n` rather than at the small parameter.
This is the estimate that survives when the small-parameter clause is unavailable, so it
carries no exceptional set either. -/
theorem explicit_formula_total_size481 {K : ℕ}
    (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
    (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ) (n : ℕ)
    (hγ : ∀ i j, ‖gammaPair481 (z i).2.2 (z j).2.2 n‖ ≤ Real.pi * n)
    (hSgb : ∀ i j, ‖Sg i j n‖ ≤ Sing n) (hS0 : 0 ≤ Sing n) :
    |(∑ i, ∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
        gammaPair481 (z i).2.2 (z j).2.2 n).re| ≤
      n * Sing n + ((K : ℝ) + 1) ^ 2 * Real.pi * n * Sing n := by
  sorry

/-! ### The assembly -/

theorem explicit_formula_reduction481_split
    (hexp : Lemma41Statement481) (hdensity : JutilaStatement481)
    (hcount : ∀ {K : ℕ} (z : Fin K → Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
      (∀ w, (univ.filter (fun i => z i = w)).card ≤
        analyticOrderNatAt (Lfun481 w.2.1) w.2.2) →
      (K : ℝ) ≤ ∑ w ∈ univ.image z, (analyticOrderNatAt (Lfun481 w.2.1) w.2.2 : ℝ))
    (hgamma : ∀ {s t : ℂ}, (1 / 2 : ℝ) ≤ s.re → (1 / 2 : ℝ) ≤ t.re →
      s.re ≤ 1 → t.re ≤ 1 → ∀ {n : ℕ}, 1 ≤ n →
        ‖gammaPair481 s t n‖ ≤ Real.pi * n)
    (η : ℝ) (hη : 0 < η) :
    ∃ (K₁ Cstar : ℕ) (A H T : ℝ), 0 < Cstar ∧ 0 ≤ A ∧ 1 ≤ H ∧ 1 ≤ T ∧
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ∃ (P : ℝ) (E : Finset ℕ), AdmissibleP131 X P ∧ E.card ≤ K₁ ∧
          (∀ r ∈ E, ∃ z ∈ zeroBox481 X H T P, z.1 = r) ∧
          (∀ n ∈ evenJ131 X, Nonexceptional131 Cstar E n →
            |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) ∧
          (∀ n ∈ evenJ131 X, |binaryMajor131 X n P| ≤ A * n * Sing n) := by
  classical
  obtain ⟨C₀, hC₀, hdens⟩ := zero_family_card_bound481 hdensity hcount
  obtain ⟨s₀, hs₀, hs₀le⟩ := singular_series_lower481
  obtain ⟨c, ε₀, B, H₀, T₀, hc, hε₀, hB, Cε, hCε, hmain⟩ := hexp
  obtain ⟨H, T, ε, hH₀, hH1, hT₀, hT1, hε, hεε₀, hAbs, hSmall⟩ :=
    absorption_constants481 c B ε₀ s₀ C₀ η H₀ T₀ hc hB hε₀ hs₀ hC₀ hη
  set K₁ : ℕ := ⌈C₀ * Real.exp (4 * H)⌉₊ + 1 with hK₁
  set Cstar : ℕ := Cε ε with hCs
  set A : ℝ := 1 + ((K₁ : ℝ) + 1) ^ 2 * Real.pi + η / 2 with hA
  have hCstar : 0 < Cstar := hCε ε
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  obtain ⟨X₁, hX₁⟩ := hmain H T hH₀ hT₀
  obtain ⟨X₂, hX₂⟩ := hdens H T hH1 hT1
  obtain ⟨X₃, hX₃⟩ := log_threshold481 H
  refine ⟨K₁, Cstar, A, H, T, hCstar, hA0, hH1, hT1, max X₁ (max X₂ X₃), ?_⟩
  intro X hX
  have hx1 : X₁ ≤ X := by omega
  have hx2 : X₂ ≤ X := by omega
  have hx3 : X₃ ≤ X := by omega
  obtain ⟨P, hP, K, z, Sg, hz01, hz0s, hbox, hmult, hSg00, hSgb, hSgε, hrem⟩ :=
    hX₁ X hx1
  have hnR : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) := fun n => Nat.cast_nonneg n
  have hlog : 2 * H ≤ Real.log X := hX₃ X hx3
  have hlogpos : 0 < Real.log X := by linarith
  have hdivH : H / Real.log X ≤ 1 / 2 := by
    rw [div_le_iff₀ hlogpos]
    linarith
  have hstrip : ∀ i : Fin (K + 1), (1 / 2 : ℝ) ≤ (z i).2.2.re ∧ (z i).2.2.re ≤ 1 := by
    intro i
    by_cases hi : i = 0
    · have hz : (z i).2.2 = 1 := by rw [hi]; exact hz0s
      rw [hz]
      norm_num
    · have hmem := hbox i hi
      simp only [zeroBox481, Set.mem_setOf_eq] at hmem
      obtain ⟨-, -, -, -, hre, hre1, -⟩ := hmem
      exact ⟨by linarith, le_of_lt hre1⟩
  have hγf : ∀ (n : ℕ), 1 ≤ n → ∀ i j,
      ‖gammaPair481 (z i).2.2 (z j).2.2 n‖ ≤ Real.pi * n :=
    fun n hn i j => hgamma (hstrip i).1 (hstrip j).1 (hstrip i).2 (hstrip j).2 hn
  have hK : (K : ℝ) ≤ C₀ * Real.exp (4 * H) := hX₂ X hx2 P hP K z hz01 hz0s hbox hmult
  have hKle : K ≤ K₁ := by
    have h1 : (K : ℝ) ≤ (⌈C₀ * Real.exp (4 * H)⌉₊ : ℝ) := le_trans hK (Nat.le_ceil _)
    have h2 : K ≤ ⌈C₀ * Real.exp (4 * H)⌉₊ := by exact_mod_cast h1
    rw [hK₁]
    omega
  refine ⟨P, (univ.erase (0 : Fin (K + 1))).image (fun i => (z i).1), hP, ?_, ?_, ?_, ?_⟩
  · have hcard : ((univ.erase (0 : Fin (K + 1))).image (fun i => (z i).1)).card ≤ K := by
      refine (Finset.card_image_le).trans ?_
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    omega
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨z i, hbox i (Finset.mem_erase.mp hi).1, rfl⟩
  · intro n hn hnonexc
    have hn1 : 1 ≤ n := (evenJ_nat131 hn).1
    have hX2n : (X : ℝ) ≤ 2 * n := by
      have h : (2 : ℝ) * X ≤ 3 * n := by
        have hnat : 2 * X ≤ 3 * n := (evenJ_nat131 hn).2.2.2
        exact_mod_cast hnat
      linarith
    have hQ0 : 0 ≤ Real.exp (-c * H) + 1 / Real.sqrt T := by
      have h1 : (0 : ℝ) < Real.exp (-c * H) := Real.exp_pos _
      have h2 : (0 : ℝ) < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
      positivity
    have hSgε' : ∀ i j, (i ≠ 0 ∨ j ≠ 0) → ‖Sg i j n‖ ≤ ε := by
      intro i j hij
      refine hSgε ε hε hεε₀ i j n hn ?_
      rcases hij with hi | hj
      · exact Or.inl (hnonexc (z i).1 (Finset.mem_image.mpr
          ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, rfl⟩))
      · exact Or.inr (hnonexc (z j).1 (Finset.mem_image.mpr
          ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩, rfl⟩))
    set Tsum : ℝ := (∑ i, ∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
      gammaPair481 (z i).2.2 (z j).2.2 n).re with hTsum
    have hrem' : |binaryMajor131 X n P - Tsum| ≤
        (2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T)) * n := by
      have hremn := hrem n hn
      rw [← hTsum] at hremn
      refine hremn.trans ?_
      calc B * ((X : ℝ) * Real.exp (-c * H) + X / Real.sqrt T)
          = X * (B * (Real.exp (-c * H) + 1 / Real.sqrt T)) := by ring
        _ ≤ (2 * n) * (B * (Real.exp (-c * H) + 1 / Real.sqrt T)) :=
            mul_le_mul_of_nonneg_right hX2n (mul_nonneg hB hQ0)
        _ = (2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T)) * n := by ring
    have h4 : |Tsum - n * Sing n| ≤ ((K : ℝ) + 1) ^ 2 * ε * Real.pi * n := by
      have h := explicit_formula_main_term481 z Sg n ε hz0s (hSg00 n hn) (hγf n hn1) hε.le hSgε'
      rw [← hTsum] at h
      exact h
    have hOffN : ((K : ℝ) + 1) ^ 2 * ε * Real.pi * n ≤ (η * s₀ / 2) * n := by
      have hsq : ((K : ℝ) + 1) ^ 2 ≤ (C₀ * Real.exp (4 * H) + 2) ^ 2 := by
        nlinarith [hK]
      calc ((K : ℝ) + 1) ^ 2 * ε * Real.pi * n
          = ((K : ℝ) + 1) ^ 2 * (ε * Real.pi * n) := by ring
        _ ≤ (C₀ * Real.exp (4 * H) + 2) ^ 2 * (ε * Real.pi * n) :=
            mul_le_mul_of_nonneg_right hsq (by positivity)
        _ = ((C₀ * Real.exp (4 * H) + 2) ^ 2 * Real.pi * ε) * n := by ring
        _ ≤ (η * s₀ / 2) * n := mul_le_mul_of_nonneg_right hSmall (hnR n)
    calc |binaryMajor131 X n P - n * Sing n|
        ≤ |binaryMajor131 X n P - Tsum| + |Tsum - n * Sing n| := abs_sub_le _ _ _
      _ ≤ (2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T)) * n +
          ((K : ℝ) + 1) ^ 2 * ε * Real.pi * n := add_le_add hrem' h4
      _ ≤ (η * s₀ / 2) * n + (η * s₀ / 2) * n :=
          add_le_add (mul_le_mul_of_nonneg_right hAbs (hnR n)) hOffN
      _ ≤ η * n * Sing n := by
          have hs : s₀ ≤ Sing n := hs₀le X n hn
          have h1 : (η * s₀ / 2) * n + (η * s₀ / 2) * n = (η * n) * s₀ := by ring
          rw [h1]
          calc (η * n) * s₀ ≤ (η * n) * Sing n :=
                mul_le_mul_of_nonneg_left hs (by positivity)
            _ = η * n * Sing n := by ring
  · intro n hn
    have hn1 : 1 ≤ n := (evenJ_nat131 hn).1
    have hX2n : (X : ℝ) ≤ 2 * n := by
      have h : (2 : ℝ) * X ≤ 3 * n := by
        have hnat : 2 * X ≤ 3 * n := (evenJ_nat131 hn).2.2.2
        exact_mod_cast hnat
      linarith
    have hQ0 : 0 ≤ Real.exp (-c * H) + 1 / Real.sqrt T := by
      have h1 : (0 : ℝ) < Real.exp (-c * H) := Real.exp_pos _
      have h2 : (0 : ℝ) < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
      positivity
    set Tsum : ℝ := (∑ i, ∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
      gammaPair481 (z i).2.2 (z j).2.2 n).re with hTsum
    have hrem' : |binaryMajor131 X n P - Tsum| ≤
        (2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T)) * n := by
      have hremn := hrem n hn
      rw [← hTsum] at hremn
      refine hremn.trans ?_
      calc B * ((X : ℝ) * Real.exp (-c * H) + X / Real.sqrt T)
          = X * (B * (Real.exp (-c * H) + 1 / Real.sqrt T)) := by ring
        _ ≤ (2 * n) * (B * (Real.exp (-c * H) + 1 / Real.sqrt T)) :=
            mul_le_mul_of_nonneg_right hX2n (mul_nonneg hB hQ0)
        _ = (2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T)) * n := by ring
    have h5 : |Tsum| ≤ n * Sing n + ((K : ℝ) + 1) ^ 2 * Real.pi * n * Sing n := by
      have h := explicit_formula_total_size481 z Sg n (hγf n hn1) (fun i j => hSgb i j n hn)
        (Sing_nonneg131 n)
      rw [← hTsum] at h
      exact h
    have hDnS : (2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T)) * n ≤
        (η / 2) * (n * Sing n) := by
      have hnS : s₀ * (n : ℝ) ≤ Sing n * n :=
        mul_le_mul_of_nonneg_right (hs₀le X n hn) (hnR n)
      calc (2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T)) * n
          ≤ (η * s₀ / 2) * n := mul_le_mul_of_nonneg_right hAbs (hnR n)
        _ = (η / 2) * (s₀ * n) := by ring
        _ ≤ (η / 2) * (Sing n * n) := mul_le_mul_of_nonneg_left hnS (by positivity)
        _ = (η / 2) * (n * Sing n) := by ring
    have hKle' : ((K : ℝ) + 1) ^ 2 ≤ ((K₁ : ℝ) + 1) ^ 2 := by
      have h : (K : ℝ) ≤ (K₁ : ℝ) := by exact_mod_cast hKle
      nlinarith
    have hoffS : ((K : ℝ) + 1) ^ 2 * Real.pi * n * Sing n ≤
        ((K₁ : ℝ) + 1) ^ 2 * Real.pi * n * Sing n := by
      have h0 : 0 ≤ Real.pi * n * Sing n :=
        mul_nonneg (mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n)) (Sing_nonneg131 n)
      calc ((K : ℝ) + 1) ^ 2 * Real.pi * n * Sing n
          = ((K : ℝ) + 1) ^ 2 * (Real.pi * n * Sing n) := by ring
        _ ≤ ((K₁ : ℝ) + 1) ^ 2 * (Real.pi * n * Sing n) :=
            mul_le_mul_of_nonneg_right hKle' h0
        _ = ((K₁ : ℝ) + 1) ^ 2 * Real.pi * n * Sing n := by ring
    have hb : |binaryMajor131 X n P| ≤ |binaryMajor131 X n P - Tsum| + |Tsum| := by
      simpa using abs_add_le (binaryMajor131 X n P - Tsum) Tsum
    calc |binaryMajor131 X n P|
        ≤ |binaryMajor131 X n P - Tsum| + |Tsum| := hb
      _ ≤ (2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T)) * n +
          (n * Sing n + ((K : ℝ) + 1) ^ 2 * Real.pi * n * Sing n) := add_le_add hrem' h5
      _ ≤ (η / 2) * (n * Sing n) +
          (n * Sing n + ((K₁ : ℝ) + 1) ^ 2 * Real.pi * n * Sing n) :=
          add_le_add hDnS (add_le_add le_rfl hoffS)
      _ = A * n * Sing n := by rw [hA]; ring

end

end LeanLab.LPZ2007

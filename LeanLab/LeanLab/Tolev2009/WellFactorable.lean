/-
AI wrote this Lean code. Codex task45.
Binary Goldbach is open.
Source: Tolev 2009, https://arxiv.org/abs/0902.2669.
The exact source pages and plain math twins are in STATEMENTS.md.
-/
import LeanLab.Tolev2009.L2Bound

open Finset Real

namespace LeanLab.Tolev2009.WellFactorable

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful LeanLab.Tolev2009.Dyadic

/-- A real function is supported on positive integers through its real level. -/
def Supported (D : ℝ) (f : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, n = 0 ∨ D < n → f n = 0

/-- Mikawa 2000 page 351, restricted to real functions and positive levels at least one. -/
def RealWellFactorable (D : ℝ) (lam : ℕ → ℝ) : Prop :=
  1 ≤ D ∧
    ∀ D₁ D₂ : ℝ, 1 ≤ D₁ → 1 ≤ D₂ → D₁ * D₂ = D →
      ∃ f g : ℕ → ℝ, Supported D₁ f ∧ Supported D₂ g ∧
        (∀ n, |f n| ≤ 1) ∧ (∀ n, |g n| ≤ 1) ∧
        ∀ n : ℕ, lam n = ∑ d ∈ n.divisors, f d * g (n / d)

/-- Zero weights are a nonempty instance of the printed factorisation condition. -/
theorem zero_wellFactorable (D : ℝ) (hD : 1 ≤ D) : RealWellFactorable D (fun _ => 0) := by
  refine ⟨hD, fun D₁ D₂ _ _ _ => ?_⟩
  refine ⟨fun _ => 0, fun _ => 0, fun _ _ => rfl, fun _ _ => rfl,
    fun _ => by norm_num, fun _ => by norm_num, fun _ => ?_⟩
  simp

/-- The factorisation with first level one forces the weight to be bounded by one. -/
theorem wellFactorable_bounded (D : ℝ) (lam : ℕ → ℝ) (h : RealWellFactorable D lam) :
    ∀ n, |lam n| ≤ 1 := by
  obtain ⟨f, g, hf, hg, hfb, hgb, he⟩ := h.2 1 D le_rfl h.1 (by ring)
  intro n
  by_cases hn : n = 0
  · subst n
    rw [he 0]
    simp
  · have hs : (∑ d ∈ n.divisors, f d * g (n / d)) = f 1 * g n := by
      rw [sum_eq_single 1]
      · simp
      · intro d hd hne
        rw [hf d (Or.inr (by
          have hdpos := Nat.pos_of_mem_divisors hd
          have : 1 < d := by omega
          exact_mod_cast this)), zero_mul]
      · intro hnot
        exact (hnot (Nat.one_mem_divisors.mpr hn)).elim
    rw [he n, hs, abs_mul]
    simpa using mul_le_mul (hfb 1) (hgb n) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

/-- The printed factorisation property implies support at the stated level. -/
theorem wellFactorable_supported (D : ℝ) (lam : ℕ → ℝ) (h : RealWellFactorable D lam) :
    Supported D lam := by
  obtain ⟨f, g, hf, hg, _, _, he⟩ := h.2 1 D le_rfl h.1 (by ring)
  intro n hn
  rw [he n]
  rcases hn with hn | hn
  · subst n; simp
  · apply sum_eq_zero
    intro d hd
    by_cases hd1 : d = 1
    · subst d
      rw [Nat.div_one, hg n (Or.inr hn), mul_zero]
    · rw [hf d (Or.inr (by
        have hdpos := Nat.pos_of_mem_divisors hd
        have : 1 < d := by omega
        exact_mod_cast this)), zero_mul]

/-- A nonzero instance exists at every level at least one. -/
theorem unit_wellFactorable (D : ℝ) (hD : 1 ≤ D) :
    RealWellFactorable D (fun n => if n = 1 then 1 else 0) := by
  let u : ℕ → ℝ := fun n => if n = 1 then 1 else 0
  have hs : ∀ T : ℝ, 1 ≤ T → Supported T u := by
    intro T hT n hn
    have hne : n ≠ 1 := by
      rintro rfl
      rcases hn with hn | hn <;> norm_num at hn
      linarith
    simp [u, hne]
  refine ⟨hD, fun D₁ D₂ hD₁ hD₂ _ => ?_⟩
  refine ⟨u, u, hs D₁ hD₁, hs D₂ hD₂, fun n => ?_, fun n => ?_, fun n => ?_⟩
  · simp only [u]; split_ifs <;> norm_num
  · simp only [u]; split_ifs <;> norm_num
  · by_cases hn : n = 1
    · subst n; simp [u]
    · change (if n = 1 then (1 : ℝ) else 0) = _
      rw [ite_eq_right hn]
      symm
      apply sum_eq_zero
      intro d _
      by_cases hd : d = 1
      · subst d; simp [u, hn]
      · simp [u, hd]

/-- The extended third level mentioned after display 5. -/
noncomputable def level49 (B : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ ((4 : ℝ) / 9) * Real.log N ^ (-B)

/-- E star with the third cutoff increased to N to four ninths times L to minus B. -/
noncomputable def Estar49 (lam : ℕ → ℝ) (l₃ : ℕ) (B : ℝ) (N : ℕ) : ℝ :=
  ∑ k₁ ∈ Icc 1 (cutoff B N), ∑ k₂ ∈ Icc 1 (cutoff B N),
    innerF (fun k l => Δ singSeries k l N) lam l₃ ⌊level49 B N⌋₊ k₁ k₂

/-- The remark on page 3 of Tolev 2009, cited to Mikawa 2000.
This is a cited Prop, not a theorem proved in this file. -/
def WellFactorableExtension : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ l₃ : ℕ, 1 ≤ l₃ → ∃ C N₀ : ℝ,
    ∀ N : ℕ, Odd N → N₀ ≤ N → ∀ lam : ℕ → ℝ,
      RealWellFactorable (level49 B N) lam →
        Estar49 lam l₃ B N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A)

/-- The extended weighted error is zero at the zero function. -/
theorem Estar49_zero (l₃ N : ℕ) (B : ℝ) : Estar49 (fun _ => 0) l₃ B N = 0 := by
  simp [Estar49, innerF]

/-- The enlarged third cutoff still has square at most N. -/
theorem level49_floor_sq_le (B : ℝ) (N : ℕ) (hB : 0 ≤ B) (hL : 1 ≤ Real.log N) :
    (⌊level49 B N⌋₊ : ℝ) ^ 2 ≤ N := by
  have hN : 1 ≤ N := by
    by_contra h
    have : N = 0 := by omega
    norm_num [this] at hL
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hf : (⌊level49 B N⌋₊ : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 9) * Real.log N ^ (-B) :=
    Nat.floor_le (by unfold level49; positivity)
  have hb : Real.log N ^ (-B) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have hr : (N : ℝ) ^ ((4 : ℝ) / 9) ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hNr (by norm_num)
  have hc : (⌊level49 B N⌋₊ : ℝ) ≤ Real.sqrt N :=
    hf.trans ((mul_le_of_le_one_right (by positivity) hb).trans hr)
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg ⌊level49 B N⌋₊) hc 2
  simpa only [Real.sq_sqrt (Nat.cast_nonneg N)] using hp

/-- The proved L2 estimate also covers the well factorable extension.
It does not require the cited Mikawa exponential sum theorem. -/
theorem wellFactorable_L2 (B : ℝ) (lam : ℕ → ℝ) (l₃ N : ℕ) (hB : 0 ≤ B)
    (h : RealWellFactorable (level49 B N) lam) (hl₃ : l₃ ≤ N) (hL : 1 ≤ Real.log N) :
    (∫ α in (0 : ℝ)..1, ‖Displays14to16.Kfun lam l₃ ⌊level49 B N⌋₊ N α‖ ^ 2) ≤
      17 * N * Real.log N ^ (20 : ℕ) :=
  L2Bound.display12_L2 lam l₃ _ N (wellFactorable_bounded _ _ h) hl₃ (level49_floor_sq_le B N hB hL) hL

end LeanLab.Tolev2009.WellFactorable

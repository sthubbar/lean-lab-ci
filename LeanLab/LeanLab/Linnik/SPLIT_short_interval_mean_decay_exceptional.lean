/-
Split unit for the exceptional-case short interval mean decay estimate of
LeanLab/Linnik/Decomp486c.lean. This file adds new declarations only: no existing
statement of the parent file is edited. The three leaf estimates below each bound one
range of the conductor sum, and the assembly combines the three into the parent statement.
-/
import LeanLab.Linnik.Decomp486c

namespace LeanLab.Linnik.Decomp486c

open Finset MeasureTheory Filter
open scoped Classical
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (excSet)

/-! ### Leaves, one per range of the conductor sum

The exceptional-case display bounds a double sum over the conductors up to the height and
the primitive characters of each conductor. The conductor sum is cut at one and at the
square root of the height, and each of the three ranges is carried by one leaf:

* `leaf_conductor_one_term`: the conductor-one range alone, where the principal main
  polynomial is subtracted;
* `leaf_low_conductor_range`: conductors from two up to the square root of the height,
  carried by the explicit formula together with the zero free region above the fifth power;
* `leaf_high_conductor_range`: conductors from the square root of the height up to the
  height itself, carried by the density estimate near one.
-/

/-- LEAF. The conductor-one range of the conductor sum. The single primitive character of
conductor one, with the principal main polynomial removed, contributes at most a constant
times e to the minus c over theta times the natural scale sqrt N over log N, uniformly over
every point of the exceptional set inside the window and every real zero of its character in
the strip. This is the first step of the exceptional-case display: the range where the
principal main polynomial is subtracted. -/
theorem leaf_conductor_one_term :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ →
          ∀ γ : ℝ, x.2.LFunction (γ : ℂ) = 0 →
            1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ → γ < 1 →
        ∑ k ∈ Ico 0 1,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (x.1 + 1) γ) (N + 1)
                  (gallagherLength N θ) m‖ ^ 2)
          ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  sorry

/-- LEAF. The low conductor range of the conductor sum. Over the conductors from two up to
the square root cut of the height, primitive characters only, the same double sum is at most
a constant times e to the minus c over theta times sqrt N over log N, uniformly in the point
of the exceptional set and in its real zero. This is the second step of the exceptional-case
display: the range carried by the explicit formula for the primitive L function together with
the zero free region above the fifth power of the height. -/
theorem leaf_low_conductor_range :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ →
          ∀ γ : ℝ, x.2.LFunction (γ : ℂ) = 0 →
            1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ → γ < 1 →
        ∑ k ∈ Ico 1 ⌊(N : ℝ) ^ (θ / 2)⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (x.1 + 1) γ) (N + 1)
                  (gallagherLength N θ) m‖ ^ 2)
          ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  sorry

/-- LEAF. The high conductor range of the conductor sum. Over the conductors from the square
root cut of the height up to the height itself, primitive characters only, the same double
sum is at most a constant times e to the minus c over theta times sqrt N over log N,
uniformly in the point of the exceptional set and in its real zero. This is the third step of
the exceptional-case display: the range carried by the density estimate near one. -/
theorem leaf_high_conductor_range :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ →
          ∀ γ : ℝ, x.2.LFunction (γ : ℂ) = 0 →
            1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ → γ < 1 →
        ∑ k ∈ Ico ⌊(N : ℝ) ^ (θ / 2)⌋₊ ⌊(N : ℝ) ^ θ⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (x.1 + 1) γ) (N + 1)
                  (gallagherLength N θ) m‖ ^ 2)
          ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  sorry

/-! ### Assembly -/

/-- Adding two exponentially decaying pieces at a common rate. Both bounds carry a
nonnegative scale, and the rate of the sum is the smaller of the two rates while its
constant is twice the larger constant. With scale zero this is trivial, so nothing here
depends on the sizes involved. -/
private lemma add_two_exponential_bounds {E₁ E₂ c c₁ c₂ C₁ C₂ θ s : ℝ} (hθ : 0 < θ)
    (hs : 0 ≤ s) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hc₁ : c ≤ c₁) (hc₂ : c ≤ c₂)
    (h₁ : E₁ ≤ C₁ * Real.exp (-c₁ / θ) * s)
    (h₂ : E₂ ≤ C₂ * Real.exp (-c₂ / θ) * s) :
    E₁ + E₂ ≤ (2 * max C₁ C₂) * Real.exp (-c / θ) * s := by
  have hexp₁ : Real.exp (-c₁ / θ) ≤ Real.exp (-c / θ) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hθ.le)
  have hexp₂ : Real.exp (-c₂ / θ) ≤ Real.exp (-c / θ) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hθ.le)
  have hpos : (0 : ℝ) ≤ Real.exp (-c / θ) := (Real.exp_pos _).le
  have h₁' : E₁ ≤ C₁ * Real.exp (-c / θ) * s :=
    h₁.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp₁ hC₁) hs)
  have h₂' : E₂ ≤ C₂ * Real.exp (-c / θ) * s :=
    h₂.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp₂ hC₂) hs)
  have hmid : E₁ + E₂ ≤ (C₁ + C₂) * Real.exp (-c / θ) * s := by
    have hsplit : C₁ * Real.exp (-c / θ) * s + C₂ * Real.exp (-c / θ) * s
        = (C₁ + C₂) * Real.exp (-c / θ) * s := by ring
    linarith
  have hCC : C₁ + C₂ ≤ 2 * max C₁ C₂ := by
    have h₁'' := le_max_left C₁ C₂
    have h₂'' := le_max_right C₁ C₂
    linarith
  exact hmid.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hpos) hs)

/-- The parent statement of this split, with the same statement text as
LeanLab/Linnik/Decomp486c.lean, proved from the three leaf estimates above. The parent
theorem of the same name is neither used nor restated as a hypothesis. -/
theorem short_interval_mean_decay_exceptional_split :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ →
          ∀ γ : ℝ, x.2.LFunction (γ : ℂ) = 0 →
            1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ → γ < 1 →
        ∑ k ∈ range ⌊(N : ℝ) ^ θ⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (x.1 + 1) γ) (N + 1)
                  (gallagherLength N θ) m‖ ^ 2)
          ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  obtain ⟨c₁, C₁, θ₁, hc₁, hC₁, hθ₁, hθ₁2, hleaf₁⟩ := leaf_conductor_one_term
  obtain ⟨c₂, C₂, θ₂, hc₂, hC₂, hθ₂, hθ₂2, hleaf₂⟩ := leaf_low_conductor_range
  obtain ⟨c₃, C₃, θ₃, hc₃, hC₃, hθ₃, hθ₃2, hleaf₃⟩ := leaf_high_conductor_range
  have hC₁₂ : (0 : ℝ) < 2 * max C₁ C₂ := by
    have h : (0 : ℝ) < max C₁ C₂ := lt_of_lt_of_le hC₁ (le_max_left _ _)
    linarith
  have hC : (0 : ℝ) < 2 * max (2 * max C₁ C₂) C₃ := by
    have h : (0 : ℝ) < max (2 * max C₁ C₂) C₃ := lt_of_lt_of_le hC₁₂ (le_max_left _ _)
    linarith
  refine ⟨min (min c₁ c₂) c₃, 2 * max (2 * max C₁ C₂) C₃, min (min θ₁ θ₂) θ₃,
    lt_min (lt_min hc₁ hc₂) hc₃, hC, lt_min (lt_min hθ₁ hθ₂) hθ₃, ?_, ?_⟩
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans hθ₁2)
  intro θ hθ hθle
  have hθ₁' : θ ≤ θ₁ := (hθle.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hθ₂' : θ ≤ θ₂ := (hθle.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hθ₃' : θ ≤ θ₃ := hθle.trans (min_le_right _ _)
  obtain ⟨N₁, hN₁⟩ := hleaf₁ θ hθ hθ₁'
  obtain ⟨N₂, hN₂⟩ := hleaf₂ θ hθ hθ₂'
  obtain ⟨N₃, hN₃⟩ := hleaf₃ θ hθ hθ₃'
  refine ⟨max (max (max N₁ N₂) N₃) 4, ?_⟩
  intro N hN x hx hxP γ hz hγlo hγ1
  have hN₄ : 4 ≤ N := (le_max_right _ _).trans hN
  have hN₁' : N₁ ≤ N :=
    ((le_max_left N₁ N₂).trans (le_max_left _ _)).trans ((le_max_left _ _).trans hN)
  have hN₂' : N₂ ≤ N :=
    ((le_max_right N₁ N₂).trans (le_max_left _ _)).trans ((le_max_left _ _).trans hN)
  have hN₃' : N₃ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have h₁ := hN₁ N hN₁' x hx hxP γ hz hγlo hγ1
  have h₂ := hN₂ N hN₂' x hx hxP γ hz hγlo hγ1
  have h₃ := hN₃ N hN₃' x hx hxP γ hz hγlo hγ1
  have hN1r : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hpow : (N : ℝ) ^ (θ / 2) ≤ (N : ℝ) ^ θ :=
    Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  have hAK : ⌊(N : ℝ) ^ (θ / 2)⌋₊ ≤ ⌊(N : ℝ) ^ θ⌋₊ := Nat.floor_mono hpow
  have hbase : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hhalf : (0 : ℝ) ≤ θ / 2 := by linarith
  have hpowhalf : (1 : ℝ) ≤ (N : ℝ) ^ (θ / 2) := Real.one_le_rpow hN1r hhalf
  have hA1 : 1 ≤ ⌊(N : ℝ) ^ (θ / 2)⌋₊ :=
    (Nat.le_floor_iff (Real.rpow_nonneg hbase (θ / 2))).mpr (by simpa using hpowhalf)
  have hs : (0 : ℝ) ≤ Real.sqrt N / Real.log N :=
    div_nonneg (Real.sqrt_nonneg _) (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).le
  set g : ℕ → ℝ := fun k => ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive), Real.pi / (2 * gallagherLength N θ) * Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ), ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (x.1 + 1) γ) (N + 1) (gallagherLength N θ) m‖ ^ 2) with hg
  have h₁g : ∑ k ∈ Ico 0 1, g k
      ≤ C₁ * Real.exp (-c₁ / θ) * (Real.sqrt N / Real.log N) := by
    rw [hg]
    exact h₁
  have h₂g : ∑ k ∈ Ico 1 ⌊(N : ℝ) ^ (θ / 2)⌋₊, g k
      ≤ C₂ * Real.exp (-c₂ / θ) * (Real.sqrt N / Real.log N) := by
    rw [hg]
    exact h₂
  have h₃g : ∑ k ∈ Ico ⌊(N : ℝ) ^ (θ / 2)⌋₊ ⌊(N : ℝ) ^ θ⌋₊, g k
      ≤ C₃ * Real.exp (-c₃ / θ) * (Real.sqrt N / Real.log N) := by
    rw [hg]
    exact h₃
  rw [Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_consecutive g (Nat.zero_le _) hAK]
  rw [← Finset.sum_Ico_consecutive g (Nat.zero_le 1) hA1]
  have hcc₁ : min (min c₁ c₂) c₃ ≤ c₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hcc₂ : min (min c₁ c₂) c₃ ≤ c₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hcc₃ : min (min c₁ c₂) c₃ ≤ c₃ := min_le_right _ _
  have hcomb := add_two_exponential_bounds hθ hs hC₁.le hC₂.le hcc₁ hcc₂ h₁g h₂g
  exact add_two_exponential_bounds hθ hs hC₁₂.le hC₃.le (le_refl _) hcc₃ hcomb h₃g

-- Axioms of the assembly: only the three leaves carry sorry.
#print axioms LeanLab.Linnik.Decomp486c.short_interval_mean_decay_exceptional_split

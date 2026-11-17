/-
Independent split of the arc decomposition step of the long coefficient replacement.
The major arc integral is the integral over a finite family of Farey arcs; the four
inputs below supply the continuity of the integrand, the containment of every arc in the
complete period, the pairwise disjointness of the arcs and the additivity of the
integral over a finite disjoint union.  The assembly uses only those four inputs, plus
an elementary change of variable on a single arc.
AI wrote the Lean code.  Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_long_prefix_replacement561

namespace LeanLab.BHP1997.Decomp561n
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e Decomp561m

/-- LEAF. Continuity step.  The integrand is the product of the two finite polynomial
sums and one character of the circle, hence a finite sum of continuous functions of the
arc variable `t`, with no hypothesis on the coefficients and none on the parity of the
frequency.  This is what makes the integrand integrable on the bounded union of arcs
used in the union step. -/
theorem leaf561_integrand_continuous561 (ε x : ℝ) (a b : ℕ → ℂ) (N : ℕ) :
    Continuous (fun t : ℝ => integrand512 ε x a b N t) := by
  have hcoe : Continuous (fun t : ℝ => (t : AddCircle (1 : ℝ))) := AddCircle.continuous_mk' 1
  have hfour : ∀ n : ℤ, Continuous (fun t : ℝ => @fourier 1 n (t : AddCircle (1 : ℝ))) :=
    fun n => (fourier n).continuous.comp hcoe
  simp only [integrand512, polynomial512]
  exact Continuous.mul (Continuous.mul
    (continuous_finset_sum _ (fun k _ => continuous_const.mul (hfour _)))
    (continuous_finset_sum _ (fun k _ => continuous_const.mul (hfour _))))
    (hfour _)

/-- LEAF. Containment step.  Every arc of the major arcs lies inside the complete
period of the circle.  The left end of the period is the reciprocal of the Farey order,
which eventually dominates the modulus cutoff, so the reduced centres sit at distance at
least `1/(M*(M+1))` above it while the half width of an arc is a logarithm power over
the block length; the right end is the same bound from below.  Only the elementary
growth of the order and the decay of the half width are used. -/
theorem leaf561_arcs_inside_period561 (ε D : ℝ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
      ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        Set.Icc ((r : ℝ) / q - Real.log x ^ (4 * D) / (q * length512 ε x))
            ((r : ℝ) / q + Real.log x ^ (4 * D) / (q * length512 ε x)) ⊆
          period512 ε x := by
  sorry

/-- LEAF. Separation step.  Two distinct arcs are disjoint.  Two different reduced
fractions with moduli at most the Farey order differ by at least the reciprocal of the
product of their moduli, while twice the half width of an arc is a logarithm power over
the block length, which is smaller than that reciprocal from some point on.  Reducedness
is what makes the two centres different rationals. -/
theorem leaf561_arcs_pairwise_disjoint561 (ε D : ℝ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ q₁ ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
      ∀ r₁ ∈ (Finset.Icc 1 q₁).filter (fun r => Nat.Coprime r q₁),
      ∀ q₂ ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
      ∀ r₂ ∈ (Finset.Icc 1 q₂).filter (fun r => Nat.Coprime r q₂),
        (q₁, r₁) ≠ (q₂, r₂) →
          Disjoint
            (Set.Icc ((r₁ : ℝ) / q₁ - Real.log x ^ (4 * D) / (q₁ * length512 ε x))
              ((r₁ : ℝ) / q₁ + Real.log x ^ (4 * D) / (q₁ * length512 ε x)))
            (Set.Icc ((r₂ : ℝ) / q₂ - Real.log x ^ (4 * D) / (q₂ * length512 ε x))
              ((r₂ : ℝ) / q₂ + Real.log x ^ (4 * D) / (q₂ * length512 ε x))) := by
  sorry

/-- LEAF. Union additivity step.  For a continuous integrand and a two level family of
closed arcs that is pairwise disjoint, the integral over the union is the iterated sum of
the integrals over the single arcs.  This is the only measure theoretic step: the arcs
are measurable, their union is a finite one, and continuity makes the integrand
integrable on each arc and on the union.  No arithmetic and no distribution hypothesis
is used. -/
theorem leaf561_union_integral561 (f : ℝ → ℂ) (hf : Continuous f)
    (S : Finset ℕ) (T : ℕ → Finset ℕ) (c w : ℕ → ℕ → ℝ)
    (hdisj : ∀ q₁ ∈ S, ∀ r₁ ∈ T q₁, ∀ q₂ ∈ S, ∀ r₂ ∈ T q₂, (q₁, r₁) ≠ (q₂, r₂) →
      Disjoint (Set.Icc (c q₁ r₁ - w q₁ r₁) (c q₁ r₁ + w q₁ r₁))
        (Set.Icc (c q₂ r₂ - w q₂ r₂) (c q₂ r₂ + w q₂ r₂))) :
    (∫ t in (⋃ q ∈ S, ⋃ r ∈ T q, Set.Icc (c q r - w q r) (c q r + w q r)), f t) =
      ∑ q ∈ S, ∑ r ∈ T q, ∫ t in Set.Icc (c q r - w q r) (c q r + w q r), f t := by
  sorry

/-- A single arc: the set integral over the closed interval equals the integral in the
local variable of the arc, with the centre moved into the integrand. -/
private theorem arc_translate561 (f : ℝ → ℂ) (c w : ℝ) (hw : 0 ≤ w) :
    ∫ t in Set.Icc (c - w) (c + w), f t = ∫ s in (-w)..w, f (c + s) := by
  have hle : c - w ≤ c + w := by linarith
  have h1 : ∫ t in Set.Icc (c - w) (c + w), f t = ∫ t in (c - w)..(c + w), f t := by
    rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc]
  have h2 : ∫ t in (c - w)..(c + w), f t = ∫ t in (-w)..w, f (t + c) := by
    rw [intervalIntegral.integral_comp_add_right (f := f) (a := -w) (b := w) (d := c)]
    rw [show -w + c = c - w by ring, show w + c = c + w by ring]
  have h3 : ∫ t in (-w)..w, f (t + c) = ∫ s in (-w)..w, f (c + s) := by
    apply intervalIntegral.integral_congr
    intro s _
    exact congrArg f (add_comm s c)
  rw [h1, h2, h3]

/-- The single frequency arc decomposition, assembled from the continuity of the
integrand, the containment of the arcs in the complete period, their pairwise
disjointness and the additivity of the integral over a finite disjoint union.
CONDITIONAL ON those four separate inputs. -/
theorem leaf_long_arc_decomposition561_split (ε D : ℝ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ (a b : ℝ → ℕ → ℂ) (N : ℕ),
      (∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) =
        ∑ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
          ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            ∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
                (Real.log x ^ (4 * D) / (q * length512 ε x)),
              integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s) := by
  obtain ⟨Xc, hXc⟩ := leaf561_arcs_inside_period561 ε D
  obtain ⟨Xd, hXd⟩ := leaf561_arcs_pairwise_disjoint561 ε D
  refine ⟨max (max Xc Xd) 1 + 1, ?_⟩
  intro x hx a b N
  have hbig : (max (max Xc Xd) 1 : ℝ) ≤ x := by linarith
  have hone : (1 : ℝ) ≤ max (max Xc Xd) 1 := le_max_right _ _
  have hx1 : (1 : ℝ) ≤ x := le_trans hone hbig
  have hxm : max Xc Xd ≤ x := le_trans (le_max_left (max Xc Xd) (1 : ℝ)) hbig
  have hxc : Xc ≤ x := le_trans (le_max_left Xc Xd) hxm
  have hxd : Xd ≤ x := le_trans (le_max_right Xc Xd) hxm
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < length512 ε x := Real.rpow_pos_of_pos hxpos _
  have hWnn : ∀ q : ℕ, 1 ≤ q → 0 ≤ Real.log x ^ (4 * D) / (q * length512 ε x) := by
    intro q hq
    apply div_nonneg (Real.rpow_nonneg (le_of_lt hlog) _)
    exact mul_nonneg (Nat.cast_nonneg q) (le_of_lt hLpos)
  have hsub : (⋃ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
        ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          Set.Icc ((r : ℝ) / q - Real.log x ^ (4 * D) / (q * length512 ε x))
            ((r : ℝ) / q + Real.log x ^ (4 * D) / (q * length512 ε x))) ⊆
      period512 ε x := by
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨q, hq, r, hr, ht⟩ := ht
    exact hXc x hxc q hq r hr ht
  have hunion : major512 ε D x =
      ⋃ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
        ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          Set.Icc ((r : ℝ) / q - Real.log x ^ (4 * D) / (q * length512 ε x))
            ((r : ℝ) / q + Real.log x ^ (4 * D) / (q * length512 ε x)) := by
    have hmaj : major512 ε D x =
        period512 ε x ∩
          ⋃ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
            ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
              Set.Icc ((r : ℝ) / q - Real.log x ^ (4 * D) / (q * length512 ε x))
                ((r : ℝ) / q + Real.log x ^ (4 * D) / (q * length512 ε x)) := rfl
    rw [hmaj]
    ext t
    constructor
    · rintro ⟨-, ht⟩
      exact ht
    · intro ht
      exact ⟨hsub ht, ht⟩
  rw [hunion]
  rw [leaf561_union_integral561 (fun t : ℝ => integrand512 ε x (a x) (b x) N t)
    (leaf561_integrand_continuous561 ε x (a x) (b x) N)
    (Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊))
    (fun q => (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q))
    (fun q r => (r : ℝ) / q)
    (fun q r => Real.log x ^ (4 * D) / (q * length512 ε x))
    (hXd x hxd)]
  refine Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (fun r hr => ?_))
  exact arc_translate561 (fun t : ℝ => integrand512 ε x (a x) (b x) N t)
    ((r : ℝ) / q) (Real.log x ^ (4 * D) / (q * length512 ε x))
    (hWnn q (Finset.mem_Icc.mp hq).1)

end LeanLab.BHP1997.Decomp561n

import LeanLab.ExceptionalSet.Decomp371d

/-!
Split of the sealed statement `leaf_poisson` of `LeanLab.ExceptionalSet.Decomp371d`
into four strictly smaller steps, plus an assembly `leaf_poisson_split` whose statement is
the sealed statement and whose proof uses only the four leaves.

The steps are the usual two halves of a Poisson summation argument:
* the summation identity itself, over the integer shifts of the modulated kernel;
* the vanishing of the Fourier transform of `K` at the two unit frequencies, which is where
  the continuity of `K` enters, since the support hypothesis only covers `|α| > 1`;
* the index bookkeeping that singles out the two integer shifts whose frequency falls in the
  unit interval;
* the collapse of the resulting series to those two terms.

AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp371d

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (eC ftR hcheck)

/-- The modulus of the exponential character is one. -/
private lemma eC_norm (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  have h : (2 * (π : ℂ) * Complex.I * (x : ℂ)) = ((2 * π * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- The exponential character is continuous. -/
private lemma eC_continuous : Continuous eC := by
  unfold eC
  fun_prop

/-- The Fourier transform `ftR K` of an integrable `K` is continuous. -/
private lemma continuous_ftR (K : ℝ → ℂ) (hK : Integrable K) : Continuous (ftR K) := by
  unfold ftR
  have key : ∀ β : ℝ, Continuous fun x : ℝ => K β * eC (-(x * β)) := by
    intro β
    exact continuous_const.mul
      (eC_continuous.comp ((continuous_id.mul continuous_const : Continuous fun x : ℝ => x * β).neg))
  have keym : ∀ ξ : ℝ, AEStronglyMeasurable (fun β : ℝ => K β * eC (-(ξ * β))) := by
    intro ξ
    exact hK.aestronglyMeasurable.mul
      (eC_continuous.comp ((continuous_const.mul continuous_id : Continuous fun β : ℝ => ξ * β).neg)).aestronglyMeasurable
  refine continuous_of_dominated (bound := fun β => ‖K β‖)
    (F := fun ξ β => K β * eC (-(ξ * β))) keym ?_ hK.norm ?_
  · intro ξ
    filter_upwards with β
    rw [norm_mul, eC_norm, mul_one]
  · filter_upwards with β
    exact key β

/-- LEAF. Poisson summation step: the sum of the modulated integer shifts of `K` equals the
sum of the Fourier transform of `K` at the shifted frequencies `v + m`, each carrying the
phase `eC (α * m)`. This is the analytic half of the proof, and it is where the
integrability of `K` is used. -/
theorem leaf_poisson_summation (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
      ∑' m : ℤ, eC (α * (m : ℝ)) * ftR K (v + (m : ℝ)) := by
  sorry

/-- LEAF. Endpoint step: the Fourier transform of `K` vanishes on the closed unit pair of
frequencies `±1` as well. The support hypothesis gives this only for `1 < |α|`; the values at
`|α| = 1` follow from continuity of `α ↦ ftR K α`, which integrability of `K` supplies. -/
theorem leaf_poisson_endpoint (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    ∀ ξ : ℝ, 1 ≤ |ξ| → ftR K ξ = 0 := by
  have hcont' : Continuous (ftR K) := continuous_ftR K hK
  have hclosed : IsClosed {ξ : ℝ | ftR K ξ = 0} := isClosed_eq hcont' continuous_const
  have hsub : {ξ : ℝ | 1 < |ξ|} ⊆ {ξ : ℝ | ftR K ξ = 0} := fun ξ hξ => hsupp ξ hξ
  have hclos : closure {ξ : ℝ | 1 < |ξ|} ⊆ {ξ : ℝ | ftR K ξ = 0} :=
    hclosed.closure_subset_iff.mpr hsub
  have hclosure : closure {ξ : ℝ | 1 < |ξ|} = {ξ : ℝ | 1 ≤ |ξ|} := by
    have hset : {ξ : ℝ | 1 < |ξ|} = Set.Ioi (1 : ℝ) ∪ Set.Iio (-1 : ℝ) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioi, Set.mem_Iio, lt_abs, lt_neg]
    rw [hset, closure_union, closure_Ioi, closure_Iio]
    ext x
    simp only [Set.mem_union, Set.mem_Ici, Set.mem_Iic, Set.mem_setOf_eq, le_abs, le_neg]
  intro ξ hξ
  exact hclos (by rw [hclosure]; exact hξ)


/-- LEAF. Index step: every integer shift `m` other than `-⌊v⌋` and `-(⌊v⌋ + 1)` puts the
frequency `v + m` at distance at least `1` from the origin. This is the only point where the
floor and fractional part of `v` are used. -/
theorem leaf_poisson_index (v : ℝ) :
    ∀ m : ℤ, m ≠ -⌊v⌋ → m ≠ -(⌊v⌋ + 1) → 1 ≤ |v + (m : ℝ)| := by
  intro m hm1 hm2
  have hdecomp : v = (⌊v⌋ : ℝ) + Int.fract v := (Int.floor_add_fract v).symm
  have hfr0 : 0 ≤ Int.fract v := Int.fract_nonneg v
  have hfr1 : Int.fract v < 1 := Int.fract_lt_one v
  set j : ℤ := ⌊v⌋ + m with hjdef
  have hj0 : j ≠ 0 := by
    intro h
    apply hm1
    have : (⌊v⌋ + m : ℤ) = 0 := h
    omega
  have hj1 : j ≠ -1 := by
    intro h
    apply hm2
    have : (⌊v⌋ + m : ℤ) = -(⌊v⌋ + 1) := by omega
    omega
  have hveq : v + (m : ℝ) = Int.fract v + (j : ℝ) := by
    have hfr : (⌊v⌋ : ℝ) + Int.fract v = v := Int.floor_add_fract v
    have hjj : (j : ℝ) = (⌊v⌋ : ℝ) + (m : ℝ) := by
      rw [hjdef]; push_cast; ring
    linarith
  rcases lt_or_ge j 1 with hlt | hge
  · have hjle : j ≤ -2 := by omega
    have hjle' : (j : ℝ) ≤ -2 := by exact_mod_cast hjle
    have hneg : v + (m : ℝ) < -1 := by rw [hveq]; linarith
    rw [abs_of_neg (by linarith)]
    linarith
  · have hge' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hge
    have hnn : 0 ≤ v + (m : ℝ) := by rw [hveq]; linarith
    rw [abs_of_nonneg hnn]
    linarith


/-- LEAF. Collapse step: by the endpoint and index steps, all but the shifts `-⌊v⌋` and
`-(⌊v⌋ + 1)` drop out of the Fourier series, and the two survivors are the terms of the
right-hand side, since `v + (-⌊v⌋) = Int.fract v` and `v + (-(⌊v⌋ + 1)) = Int.fract v - 1`. -/
theorem leaf_poisson_collapse (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' m : ℤ, eC (α * (m : ℝ)) * ftR K (v + (m : ℝ))) =
      eC (-(α * (⌊v⌋ : ℝ))) * ftR K (Int.fract v) +
        eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) * ftR K (Int.fract v - 1) := by
  have hzero : ∀ m : ℤ, m ∉ ({-⌊v⌋, -(⌊v⌋ + 1)} : Finset ℤ) →
      eC (α * (m : ℝ)) * ftR K (v + (m : ℝ)) = 0 := by
    intro m hm
    have hm1 : m ≠ -⌊v⌋ := by
      intro h; exact hm (by simp [h])
    have hm2 : m ≠ -(⌊v⌋ + 1) := by
      intro h; exact hm (by simp [h])
    have h1 := leaf_poisson_index v m hm1 hm2
    rw [leaf_poisson_endpoint K hK hcont hsupp _ h1, mul_zero]
  rw [tsum_eq_sum hzero]
  have hne : (-⌊v⌋ : ℤ) ≠ -(⌊v⌋ + 1) := by omega
  rw [Finset.sum_pair hne]
  have hfr : (⌊v⌋ : ℝ) + Int.fract v = v := Int.floor_add_fract v
  have e1 : v + ((-⌊v⌋ : ℤ) : ℝ) = Int.fract v := by push_cast; linarith
  have e2 : v + ((-(⌊v⌋ + 1) : ℤ) : ℝ) = Int.fract v - 1 := by push_cast; linarith
  rw [e1, e2]
  have p1 : α * ((-⌊v⌋ : ℤ) : ℝ) = -(α * (⌊v⌋ : ℝ)) := by push_cast; ring
  have p2 : α * ((-(⌊v⌋ + 1) : ℤ) : ℝ) = -(α * ((⌊v⌋ + 1 : ℤ) : ℝ)) := by push_cast; ring
  rw [p1, p2]


/-- Assembly: the sealed statement, from the summation leaf and the collapse leaf. -/
theorem leaf_poisson_split (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
      eC (-(α * (⌊v⌋ : ℝ))) * ftR K (Int.fract v) +
        eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) * ftR K (Int.fract v - 1) := by
  rw [leaf_poisson_summation K hK hcont hsupp v α,
    leaf_poisson_collapse K hK hcont hsupp v α]

end LeanLab.ExceptionalSet.Decomp371d

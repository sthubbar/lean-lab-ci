/-
Split of `lower_short_weight_analytic` in LeanLab.BHP1997.DecompC165d into four leaves.
The sealed statement is unchanged; the target theorem is neither imported nor used.

The statement asks for one Buchstab weight `ω`, one divisor exponent `B0`, one `ε`-threshold
`η`, and then for every admissible pair `(B, ε)` a density `v0` and a coefficient family `b0`
on the short interval, such that `v0` is at least one minus the two discarded Buchstab
integrals, the family obeys the short weight condition `RightConditions`, and the family is
pointwise dominated by the prime indicator on the short interval.

The split separates four steps. Leaf 1 supplies the Buchstab weight with its zero extension.
Leaf 2 supplies the two quantifiers and the range conversion `ε < η → ε ≤ 1/10^8`. Leaf 3 is
the construction of the normalised short coefficient together with its divisor bound, its
centred character mean value and the pointwise domination of the prime indicator; it also
carries the density ledger against the two discarded integrals. Leaf 4 is the remaining
exceptional character average, taken conditionally on the two boundedness properties of the
coefficient family that leaf 3 produces. The assembly below has no sorry.

The two analytic leaves remain OPEN. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165d
import LeanLab.BHP1997.DecompC165b
import LeanLab.BHP1997.ShortConditions308
import LeanLab.BHP1997.Decomp387g
import LeanLab.BHP1997.Decomp387b
import LeanLab.BHP1997.InstancesC165

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! ### Delay-equation solver for the Buchstab weight

The method-of-steps block below is carried over from the lab's
`LeanLab.ChenDoubleSieve.Decomp275b` (its own `DelaySolver` namespace, where the lemmas are
`private`), so that leaf 1 can be closed without adding an import. It solves
`X' u = k u * X (u - 1)` with prescribed data on `[1, 2]`. -/
namespace LowerShortDelay
open Set MeasureTheory intervalIntegral Filter
open scoped Topology

set_option maxHeartbeats 4000000 in
/-- One-layer existence for the scalar delay equation `X' u = k u * X (u - 1)`.
`X` is produced on `Icc 1 (N + 2)` with the integral form of the equation. -/
private theorem delay_layer_exists (k : ℝ → ℝ) (hk : ContinuousOn k (Set.Ici (2 : ℝ)))
    (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Icc (1 : ℝ) 2)) :
    ∀ N : ℕ, ∃ X : ℝ → ℝ,
      ContinuousOn X (Set.Icc (1 : ℝ) ((N : ℝ) + 2)) ∧
      (∀ u ∈ Set.Icc (1 : ℝ) (2 : ℝ), X u = φ u) ∧
      (∀ u ∈ Set.Icc (2 : ℝ) ((N : ℝ) + 2), X u = X 2 + ∫ t in (2 : ℝ)..u, k t * X (t - 1)) := by
  intro N
  induction N with
  | zero =>
    have h2 : (((0 : ℕ) : ℝ) + 2) = (2 : ℝ) := by norm_num
    refine ⟨fun u => if u ≤ (2 : ℝ) then φ u else 0, ?_, ?_, ?_⟩
    · rw [h2]
      exact (continuousOn_congr (fun u hu => by simp [hu.2])).mpr hφ
    · intro u hu
      simp [hu.2]
    · intro u hu
      rw [h2] at hu
      have hu2 : u = 2 := le_antisymm hu.2 hu.1
      subst hu2
      simp
  | succ n ih =>
    obtain ⟨X, hcont, hφX, heq⟩ := ih
    have hidx : ((((n + 1 : ℕ)) : ℝ) + 2) = (n : ℝ) + 2 + 1 := by push_cast; ring
    have hc1 : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hc2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hc3 : (n : ℝ) + 2 ≤ (n : ℝ) + 2 + 1 := by norm_num
    have hfcont : ∀ a b : ℝ, 2 ≤ a → b ≤ (n : ℝ) + 2 + 1 →
        ContinuousOn (fun t : ℝ => k t * X (t - 1)) (Set.Icc a b) := by
      intro a b ha hb
      have hk' : ContinuousOn k (Set.Icc a b) := by
        refine hk.mono ?_
        intro x hx
        simp only [Set.mem_Ici]
        linarith [hx.1]
      have hXc : ContinuousOn (fun t : ℝ => X (t - 1)) (Set.Icc a b) := by
        refine hcont.comp (continuous_id.sub continuous_const).continuousOn ?_
        intro t ht
        simp only [Set.mem_Icc]
        constructor
        · linarith [ht.1]
        · linarith [ht.2]
      exact hk'.mul hXc
    have hub : ∀ a b : ℝ, a ≤ b → 2 ≤ a → b ≤ (n : ℝ) + 2 + 1 →
        ContinuousOn (fun t : ℝ => k t * X (t - 1)) (uIcc a b) := by
      intro a b hab ha hb
      rw [uIcc_of_le hab]
      exact hfcont a b ha hb
    set X' : ℝ → ℝ := fun u =>
      if u ≤ (n : ℝ) + 2 then X u
      else X ((n : ℝ) + 2) + ∫ t in ((n : ℝ) + 2)..u, k t * X (t - 1) with hX'
    have hstep : ∀ u : ℝ, X' u = if u ≤ (n : ℝ) + 2 then X u
        else X ((n : ℝ) + 2) + ∫ t in ((n : ℝ) + 2)..u, k t * X (t - 1) :=
      fun u => congrFun hX' u
    refine ⟨X', ?_, ?_, ?_⟩
    · rw [hidx]
      have hun : Set.Icc (1 : ℝ) ((n : ℝ) + 2) ∪ Set.Icc ((n : ℝ) + 2) ((n : ℝ) + 2 + 1) =
          Set.Icc (1 : ℝ) ((n : ℝ) + 2 + 1) := Icc_union_Icc_eq_Icc hc1 hc3
      rw [← hun]
      refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
      · refine hcont.congr ?_
        intro u hu
        rw [hstep, if_pos hu.2]
      · have hint : IntegrableOn (fun t : ℝ => k t * X (t - 1))
            (uIcc ((n : ℝ) + 2) ((n : ℝ) + 2 + 1)) :=
          (hub _ _ hc3 hc2 le_rfl).integrableOn_compact isCompact_uIcc
        have hprim : ContinuousOn
            (fun u => X ((n : ℝ) + 2) + ∫ t in ((n : ℝ) + 2)..u, k t * X (t - 1))
            (Set.Icc ((n : ℝ) + 2) ((n : ℝ) + 2 + 1)) := by
          have h := (continuousOn_const (c := X ((n : ℝ) + 2))).add
            (continuousOn_primitive_interval hint)
          rwa [uIcc_of_le hc3] at h
        refine hprim.congr ?_
        intro u hu
        rw [hstep]
        by_cases h : u ≤ (n : ℝ) + 2
        · rw [if_pos h]
          have hue : u = (n : ℝ) + 2 := le_antisymm h hu.1
          subst hue
          simp
        · rw [if_neg h]
    · intro u hu
      have hu2 : u ≤ (n : ℝ) + 2 := by linarith [hu.2, hc2]
      rw [hstep, if_pos hu2]
      exact hφX u hu
    · rw [hidx]
      intro u hu
      have hX'2 : X' 2 = X 2 := by
        rw [hstep, if_pos hc2]
      rw [hX'2]
      by_cases h : u ≤ (n : ℝ) + 2
      · have hX'u : X' u = X u := by
          rw [hstep, if_pos h]
        rw [hX'u, heq u ⟨hu.1, h⟩]
        congr 1
        refine integral_congr (fun t ht => ?_)
        rw [uIcc_of_le hu.1] at ht
        have hle : t - 1 ≤ (n : ℝ) + 2 := by linarith [ht.2]
        rw [hstep, if_pos hle]
      · have hX'u : X' u = X ((n : ℝ) + 2) + ∫ t in ((n : ℝ) + 2)..u, k t * X (t - 1) := by
          rw [hstep, if_neg h]
        rw [hX'u, heq ((n : ℝ) + 2) ⟨hc2, le_rfl⟩, add_assoc]
        have hleu : u ≤ (n : ℝ) + 2 + 1 := hu.2
        have hAB : IntervalIntegrable (fun t : ℝ => k t * X (t - 1)) volume (2 : ℝ)
            ((n : ℝ) + 2) :=
          (hub 2 ((n : ℝ) + 2) (by linarith) (by norm_num) (by linarith)).intervalIntegrable
        have hBC : IntervalIntegrable (fun t : ℝ => k t * X (t - 1)) volume ((n : ℝ) + 2) u :=
          (hub ((n : ℝ) + 2) u (le_of_not_ge h) hc2 hleu).intervalIntegrable
        rw [integral_add_adjacent_intervals hAB hBC]
        congr 1
        refine integral_congr (fun t ht => ?_)
        rw [uIcc_of_le hu.1] at ht
        have hle : t - 1 ≤ (n : ℝ) + 2 := by linarith [ht.2]
        rw [hstep, if_pos hle]

set_option maxHeartbeats 4000000 in
/-- Global existence for the scalar delay equation `X' u = k u * X (u - 1)`
with prescribed values on `[1, 2]`. -/
private theorem delay_exists (k : ℝ → ℝ) (hk : ContinuousOn k (Set.Ici (2 : ℝ)))
    (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Icc (1 : ℝ) 2)) :
    ∃ X : ℝ → ℝ, ContinuousOn X (Set.Ici (1 : ℝ)) ∧
      (∀ u ∈ Set.Icc (1 : ℝ) 2, X u = φ u) ∧
      (∀ u : ℝ, 2 ≤ u → X u = X 2 + ∫ t in (2 : ℝ)..u, k t * X (t - 1)) := by
  classical
  have hex : ∀ N : ℕ, ∃ X : ℝ → ℝ,
      ContinuousOn X (Set.Icc (1 : ℝ) ((N : ℝ) + 2)) ∧
      (∀ u ∈ Set.Icc (1 : ℝ) (2 : ℝ), X u = φ u) ∧
      (∀ u ∈ Set.Icc (2 : ℝ) ((N : ℝ) + 2),
        X u = X 2 + ∫ t in (2 : ℝ)..u, k t * X (t - 1)) :=
    delay_layer_exists k hk φ hφ
  -- two layer solutions agree on the common interval
  have agree : ∀ (N M : ℕ) (X Y : ℝ → ℝ),
      (∀ u ∈ Set.Icc (1 : ℝ) 2, X u = φ u) →
      (∀ u ∈ Set.Icc (2 : ℝ) ((N : ℝ) + 2),
        X u = X 2 + ∫ t in (2 : ℝ)..u, k t * X (t - 1)) →
      (∀ u ∈ Set.Icc (1 : ℝ) 2, Y u = φ u) →
      (∀ u ∈ Set.Icc (2 : ℝ) ((M : ℝ) + 2),
        Y u = Y 2 + ∫ t in (2 : ℝ)..u, k t * Y (t - 1)) →
      ∀ u ∈ Set.Icc (1 : ℝ) (((min N M : ℕ) : ℝ) + 2), X u = Y u := by
    intro N M X Y hXφ hXe hYφ hYe
    have key : ∀ n : ℕ, n ≤ N → n ≤ M → ∀ u ∈ Set.Icc (1 : ℝ) ((n : ℝ) + 2), X u = Y u := by
      intro n
      induction n with
      | zero =>
        intro _ _ u hu
        have hu2 : u ≤ 2 := by
          simpa using hu.2
        rw [hXφ u ⟨hu.1, hu2⟩, hYφ u ⟨hu.1, hu2⟩]
      | succ n ih =>
        intro hnN hnM u hu
        have hidx : (((n + 1 : ℕ)) : ℝ) + 2 = (n : ℝ) + 2 + 1 := by push_cast; ring
        rw [hidx] at hu
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        by_cases h : u ≤ (n : ℝ) + 2
        · exact ih (by omega) (by omega) u ⟨hu.1, h⟩
        · have hgt : (n : ℝ) + 2 < u := not_le.mp h
          have hu2 : (2 : ℝ) ≤ u := by linarith
          have hcast : ((n + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
          have hcastM : ((n + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hnM
          have huN : u ≤ (N : ℝ) + 2 := by push_cast at hcast; linarith [hu.2]
          have huM : u ≤ (M : ℝ) + 2 := by push_cast at hcastM; linarith [hu.2]
          rw [hXe u ⟨hu2, huN⟩, hYe u ⟨hu2, huM⟩]
          congr 1
          · exact ih (by omega) (by omega) 2 ⟨by norm_num, by linarith⟩
          · refine integral_congr (fun t ht => ?_)
            rw [uIcc_of_le hu2] at ht
            have ht1 : (1 : ℝ) ≤ t - 1 := by linarith [ht.1]
            have ht2 : t - 1 ≤ (n : ℝ) + 2 := by linarith [ht.2, hu.2]
            rw [ih (by omega) (by omega) (t - 1) ⟨ht1, ht2⟩]
    intro u hu
    refine key (min N M) (min_le_left _ _) (min_le_right _ _) u ⟨hu.1, ?_⟩
    rw [Nat.cast_min] at hu ⊢
    rcases le_total (N : ℝ) (M : ℝ) with h | h
    · rw [min_eq_left h] at hu ⊢
      exact hu.2
    · rw [min_eq_right h] at hu ⊢
      exact hu.2
  choose Xc hXc using hex
  -- the index of the layer used at a point
  set Nf : ℝ → ℕ := fun u => max 1 ⌈u⌉₊ with hNfdef
  have hNfbig : ∀ u : ℝ, u ≤ (Nf u : ℝ) + 2 := by
    intro u
    have h1 : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
    have h2 : (⌈u⌉₊ : ℝ) ≤ (Nf u : ℝ) := by
      rw [hNfdef]
      exact_mod_cast le_max_right 1 ⌈u⌉₊
    linarith
  set X : ℝ → ℝ := fun u => Xc (Nf u) u with hXdef
  have hXval : ∀ v : ℝ, X v = Xc (Nf v) v := fun v => congrFun hXdef v
  have hXeq : ∀ (N M : ℕ) (u : ℝ), u ∈ Set.Icc (1 : ℝ) (((min N M : ℕ) : ℝ) + 2) →
      Xc N u = Xc M u :=
    fun N M u hu => agree N M (Xc N) (Xc M) (hXc N).2.1 (hXc N).2.2 (hXc M).2.1 (hXc M).2.2 u hu
  have hmem : ∀ (N M : ℕ) (u : ℝ), 1 ≤ u → u ≤ (N : ℝ) + 2 → u ≤ (M : ℝ) + 2 →
      u ∈ Set.Icc (1 : ℝ) (((min N M : ℕ) : ℝ) + 2) := by
    intro N M u h1 hN hM
    refine ⟨h1, ?_⟩
    rw [Nat.cast_min]
    rcases le_total (N : ℝ) (M : ℝ) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hφX : ∀ u ∈ Set.Icc (1 : ℝ) 2, X u = φ u := by
    intro u hu
    rw [hXval]
    exact (hXc (Nf u)).2.1 u hu
  have hXint : ∀ u : ℝ, 2 ≤ u → X u = X 2 + ∫ t in (2 : ℝ)..u, k t * X (t - 1) := by
    intro u hu
    have hstep := (hXc (Nf u)).2.2 u ⟨hu, hNfbig u⟩
    rw [hXval, hstep]
    congr 1
    · rw [hXval]
      exact hXeq (Nf u) (Nf 2) 2
        (hmem _ _ 2 (by norm_num) (by linarith [hNfbig u]) (hNfbig 2))
    · refine integral_congr (fun t ht => ?_)
      rw [uIcc_of_le hu] at ht
      have ht1 : (1 : ℝ) ≤ t - 1 := by linarith [ht.1]
      have htle : t - 1 ≤ (Nf u : ℝ) + 2 := by linarith [ht.2, hNfbig u]
      rw [hXval]
      rw [hXeq (Nf u) (Nf (t - 1)) (t - 1) (hmem _ _ _ ht1 htle (hNfbig (t - 1)))]
  have hcontIcc : ∀ n : ℕ, ContinuousOn X (Set.Icc (1 : ℝ) ((n : ℝ) + 2)) := by
    intro n
    refine ((hXc n).1).congr ?_
    intro u hu
    rw [hXval]
    exact hXeq (Nf u) n u (hmem _ _ _ hu.1 (hNfbig u) hu.2)
  have hcont : ContinuousOn X (Set.Ici (1 : ℝ)) := by
    intro u hu
    obtain ⟨n, hn⟩ := exists_nat_gt u
    have hun : Set.Icc (1 : ℝ) ((n : ℝ) + 2) ∪ Set.Ioi ((n : ℝ) + 2) = Set.Ici (1 : ℝ) := by
      ext x
      simp only [mem_union, Set.mem_Icc, Set.mem_Ioi, Set.mem_Ici]
      constructor
      · rintro (⟨h1, _⟩ | h)
        · exact h1
        · linarith
      · intro hx
        by_cases h : x ≤ (n : ℝ) + 2
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr (not_le.mp h)
    rw [← hun]
    refine ContinuousWithinAt.union (hcontIcc n u ⟨hu, by linarith⟩) ?_
    refine continuousWithinAt_of_notMem_closure ?_
    simp only [closure_Ioi, Set.mem_Ici]
    linarith
  exact ⟨X, hcont, hφX, hXint⟩

set_option maxHeartbeats 1000000 in
/-- Derivative form of the delay equation. -/
private theorem delay_hasDerivAt (k : ℝ → ℝ) (hk : ContinuousOn k (Set.Ici (2 : ℝ)))
    (X : ℝ → ℝ) (hX : ContinuousOn X (Set.Ici (1 : ℝ)))
    (hint : ∀ u : ℝ, 2 ≤ u → X u = X 2 + ∫ t in (2 : ℝ)..u, k t * X (t - 1))
    {u : ℝ} (hu : 2 < u) : HasDerivAt X (k u * X (u - 1)) u := by
  have hfcont : ContinuousOn (fun t : ℝ => k t * X (t - 1)) (Set.Ici (2 : ℝ)) := by
    intro x hx
    have h1 : ContinuousWithinAt k (Set.Ici (2 : ℝ)) x := hk x hx
    have h2 : ContinuousWithinAt (fun t : ℝ => X (t - 1)) (Set.Ici (2 : ℝ)) x := by
      have hx2 : (2 : ℝ) ≤ x := hx
      refine ContinuousWithinAt.comp (hX (x - 1) (by simp only [Set.mem_Ici]; linarith))
        (continuous_id.sub continuous_const).continuousWithinAt ?_
      intro t ht
      simp only [Set.mem_Ici] at ht ⊢
      linarith
    exact h1.mul h2
  have hcont2 : ContinuousOn (fun t : ℝ => k t * X (t - 1)) (uIcc (2 : ℝ) u) := by
    rw [uIcc_of_le (le_of_lt hu)]
    exact hfcont.mono (fun x hx => hx.1)
  have hInt : IntervalIntegrable (fun t : ℝ => k t * X (t - 1)) volume (2 : ℝ) u :=
    hcont2.intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter (fun t : ℝ => k t * X (t - 1)) (𝓝 u) :=
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
      (hfcont.mono (fun x hx => le_of_lt hx))) u (by simpa only [Set.mem_Ioi] using hu)
  have hfu : ContinuousAt (fun t : ℝ => k t * X (t - 1)) u :=
    hfcont.continuousAt (Ici_mem_nhds hu)
  have h1 : HasDerivAt (fun v : ℝ => ∫ t in (2 : ℝ)..v, k t * X (t - 1))
      (k u * X (u - 1)) u := intervalIntegral.integral_hasDerivAt_right hInt hmeas hfu
  have h2 : HasDerivAt (fun v : ℝ => X 2 + ∫ t in (2 : ℝ)..v, k t * X (t - 1))
      (k u * X (u - 1)) u := h1.const_add (X 2)
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hu] with v hv
  exact hint v hv.le

/-- Buchstab's function, extended by zero below one: leaf 1's witness. -/
private theorem buchstab_exists_zero_below_one :
    ∃ ω : ℝ → ℝ,
      LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω ∧
      LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω := by
  have hk : ContinuousOn (fun t : ℝ => 1 / (t - 1)) (Set.Ici (2 : ℝ)) := by
    intro x hx
    have hx2 : (2 : ℝ) ≤ x := hx
    have hden : (0 : ℝ) < x - 1 := by linarith
    exact (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
      (ne_of_gt hden)).continuousWithinAt
  obtain ⟨X, hXc, hXφ, hXint⟩ :=
    delay_exists (fun t : ℝ => 1 / (t - 1)) hk (fun _ => 1) continuousOn_const
  refine ⟨fun u => if u < 1 then (0 : ℝ) else X u / u, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · have hcont : ContinuousOn (fun u : ℝ => X u / u) (Set.Ici (1 : ℝ)) := by
        refine hXc.div continuousOn_id ?_
        intro u hu
        have hu1 : (1 : ℝ) ≤ u := hu
        exact ne_of_gt (by linarith)
      refine hcont.congr ?_
      intro u hu
      have hnu : ¬ (u < 1) := not_lt.mpr hu
      simp only [hnu, ↓reduceIte]
    · intro u h1 h2
      have hnu : ¬ (u < 1) := not_lt.mpr h1
      simp only [hnu, ↓reduceIte, hXφ u ⟨h1, h2⟩]
    · intro u hu
      have hu1 : (1 : ℝ) < u - 1 := by linarith
      have hderiv : HasDerivAt X (1 / (u - 1) * X (u - 1)) u :=
        delay_hasDerivAt (fun t : ℝ => 1 / (t - 1)) hk X hXc hXint hu
      have hd : HasDerivAt X (X (u - 1) / (u - 1)) u := by
        convert hderiv using 1
        field_simp
      have hval : (fun v : ℝ => v * (if v < 1 then (0 : ℝ) else X v / v)) =ᶠ[𝓝 u] X := by
        filter_upwards [Ioi_mem_nhds (show (1 : ℝ) < u by linarith)] with v hv
        have hv1 : (1 : ℝ) < v := hv
        have hnv : ¬ (v < 1) := not_lt.mpr hv1.le
        have hv0 : v ≠ 0 := ne_of_gt (by linarith)
        simp only [hnv, ↓reduceIte]
        field_simp
      have hw : (fun u : ℝ => if u < 1 then (0 : ℝ) else X u / u) (u - 1) =
          X (u - 1) / (u - 1) := by
        have hnu : ¬ (u - 1 < 1) := not_lt.mpr hu1.le
        simp only [hnu, ↓reduceIte]
      rw [hw]
      exact hd.congr_of_eventuallyEq hval
  · intro u hu
    have hnu : u < 1 := hu
    simp only [hnu, ↓reduceIte]

end LowerShortDelay

/-- LEAF 1 of 4. Step: choose the Buchstab weight. One function on the reals that solves the
defining Buchstab equations above one and is extended by zero below one, so that both the
density integrals and the zero extension of the statement have their argument.

Non-vacuity: the reading `ω = 0` fails the equations, but the construction of the standard
Buchstab function from a linear sieve pair gives a witness, so the leaf is not vacuous. The
leaf asserts nothing about any coefficient family on the short interval, so it is strictly
easier than the statement. -/
theorem leaf_buchstab_model_exists :
    ∃ ω : ℝ → ℝ,
      LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω ∧
      LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω :=
  LowerShortDelay.buchstab_exists_zero_below_one

/-- LEAF 2 of 4. Step: fix the two numeric quantifiers and convert the range restriction.
There is a divisor exponent `B0` and a threshold `η` with `0 < η`, `η ≤ 1/10^8`, such that
every admissible pair `B0 ≤ B`, `0 < ε`, `ε < η` gives `0 < ε` and `ε ≤ 1/10^8`.

The smallness of `η` is what lets the two discarded Buchstab integrals be evaluated at any
`ε` the statement allows. Non-vacuity: `B0 = 0` and `η = 1/10^8` satisfy all four conditions,
so the leaf is not vacuous. Tested at the degenerate readings `ε = η`, `ε → 0` and `B = B0`:
the conclusion is then `0 < ε` and `ε ≤ 1/10^8`, both true. -/
theorem leaf_thresholds :
    ∃ B0 η : ℝ, 0 < η ∧ η ≤ 1/10^8 ∧
      ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η → 0 < ε ∧ ε ≤ 1/10^8 := by
  refine ⟨0, 1 / 10^8, by norm_num, le_rfl, ?_⟩
  intro B ε _ hε hεη
  exact ⟨hε, le_of_lt hεη⟩

/-- Any density `v0` satisfying the Buchstab ledger inequality of `leaf_centered_character_mean_value`
on `(0, 1/10^8]` is strictly greater than `0.05`. Consequently `v0 > 0`, which rules out
any non-positive witness such as `b0 = 0` via `DecompC165b.right_density_mono`. -/
theorem leaf_lower_density_gt
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε v0 : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hv0 : 1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0) :
    0.05 < v0 :=
  lower_density_of_e2_bound hω hz (le_of_lt hε) hε8
    (lower_two_integral_bound hω hz (le_of_lt hε) hε8) hv0

/-- Obstruction to a non-positive short-interval weight in `leaf_centered_character_mean_value`:
no coefficient family `b0` that is eventually non-positive on `rightInterval ε x` can satisfy both
the Buchstab density ledger and `RightConditions ε B v0 b0`. -/
theorem leaf_nonpos_weight_obstruction
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε v0 : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    {b0 : ℝ → ℕ → ℝ}
    (hv0 : 1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0)
    (hrc : RightConditions ε B v0 b0)
    (hnonpos : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, b0 x m ≤ 0) :
    False := by
  have hv0_gt : 0.05 < v0 := leaf_lower_density_gt hω hz hε hε8 hv0
  have hrc0 : RightConditions ε 1 0 (fun _ _ => 0) :=
    InstancesC165.right_conditions_zero ε
  have hv0_le : v0 ≤ 0 :=
    DecompC165b.right_density_mono hε hrc hrc0 hnonpos
  linarith

/-! ### Inlined proof of LEAF 3 from the sibling split module

The module `LeanLab.BHP1997.SPLIT_leaf_centered_character_mean_value` proves this exact
leaf sorry-free, but that module imports this one, so importing it would be a cycle. Its
proof is carried here as private helpers instead, so that leaf 3 closes with no new import.
Every declaration below is private and is used only by that leaf. -/

/-! ### Abel summation on `Ioc` -/

private theorem abel_id (f : ℕ → ℂ) (g : ℕ → ℝ) (L : ℕ) :
    ∀ U : ℕ, L ≤ U →
      ∑ m ∈ Finset.Ioc L U, f m * (g m : ℂ) =
        (∑ m ∈ Finset.Ioc L U, f m) * (g (U + 1) : ℂ) -
          ∑ m ∈ Finset.Ioc L U, ((g (m + 1) - g m : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc L m, f k) := by
  intro U
  induction U with
  | zero =>
    intro hU
    have hL : L = 0 := Nat.le_zero.mp hU
    subst hL
    simp
  | succ n ih =>
    intro hU
    rcases Nat.lt_or_ge n L with hn | hn
    · have hn1 : n + 1 = L := by omega
      subst hn1
      simp
    · have h := ih hn
      have hgg : ∑ m ∈ Finset.Ioc L (n + 1), f m * (g m : ℂ) =
          (∑ m ∈ Finset.Ioc L n, f m * (g m : ℂ)) + f (n + 1) * (g (n + 1) : ℂ) :=
        Finset.sum_Ioc_succ_top hn _
      have hff : ∑ m ∈ Finset.Ioc L (n + 1), f m =
          (∑ m ∈ Finset.Ioc L n, f m) + f (n + 1) :=
        Finset.sum_Ioc_succ_top hn _
      have hSS : ∑ m ∈ Finset.Ioc L (n + 1),
            ((g (m + 1) - g m : ℝ) : ℂ) * (∑ k ∈ Finset.Ioc L m, f k) =
          (∑ m ∈ Finset.Ioc L n, ((g (m + 1) - g m : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc L m, f k)) +
            ((g (n + 1 + 1) - g (n + 1) : ℝ) : ℂ) * (∑ k ∈ Finset.Ioc L (n + 1), f k) :=
        Finset.sum_Ioc_succ_top hn _
      rw [hgg, hff, hSS, h, Finset.sum_Ioc_succ_top hn f]
      push_cast
      ring

private theorem abel_telescope (g : ℕ → ℝ) (L : ℕ) :
    ∀ U : ℕ, L ≤ U →
      ∑ m ∈ Finset.Ioc L U, (g (m + 1) - g m) = g (U + 1) - g (L + 1) := by
  intro U
  induction U with
  | zero =>
    intro hU
    have hL : L = 0 := Nat.le_zero.mp hU
    subst hL
    simp
  | succ n ih =>
    intro hU
    rcases Nat.lt_or_ge n L with hn | hn
    · have hn1 : n + 1 = L := by omega
      subst hn1
      simp
    · rw [Finset.sum_Ioc_succ_top hn, ih hn]
      ring

/-- Partial summation: a monotone weight times a summand with bounded prefixes. -/
private theorem abel_bound {f : ℕ → ℂ} {g : ℕ → ℝ} {L U : ℕ} {K : ℝ}
    (hLU : L ≤ U)
    (hg0 : ∀ m, L ≤ m → 0 ≤ g m)
    (hmono : ∀ m, L ≤ m → m ≤ U → g m ≤ g (m + 1))
    (hK : ∀ u, L ≤ u → u ≤ U → ‖∑ k ∈ Finset.Ioc L u, f k‖ ≤ K)
    (hKU : 0 ≤ K) :
    ‖∑ m ∈ Finset.Ioc L U, f m * (g m : ℂ)‖ ≤ K * g (U + 1) + K * g (U + 1) := by
  have hid := abel_id f g L U hLU
  have h1 : ‖(∑ m ∈ Finset.Ioc L U, f m) * (g (U + 1) : ℂ)‖ ≤ K * g (U + 1) := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 (U + 1) (by omega))]
    exact mul_le_mul_of_nonneg_right (hK U hLU le_rfl) (hg0 (U + 1) (by omega))
  have h2 : ‖∑ m ∈ Finset.Ioc L U, ((g (m + 1) - g m : ℝ) : ℂ) *
      (∑ k ∈ Finset.Ioc L m, f k)‖ ≤ K * g (U + 1) := by
    have hstep : ∀ m ∈ Finset.Ioc L U,
        ‖((g (m + 1) - g m : ℝ) : ℂ) * (∑ k ∈ Finset.Ioc L m, f k)‖ ≤
          (g (m + 1) - g m) * K := by
      intro m hm
      obtain ⟨hm1, hm2⟩ := Finset.mem_Ioc.mp hm
      have hd : 0 ≤ g (m + 1) - g m := by
        have := hmono m (le_of_lt hm1) hm2
        linarith
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_left (hK m (le_of_lt hm1) hm2) hd
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [← Finset.sum_mul, abel_telescope g L U hLU]
    have hle : g (U + 1) - g (L + 1) ≤ g (U + 1) := by
      have : 0 ≤ g (L + 1) := hg0 (L + 1) (by omega)
      linarith
    calc (g (U + 1) - g (L + 1)) * K ≤ g (U + 1) * K :=
          mul_le_mul_of_nonneg_right hle hKU
      _ = K * g (U + 1) := by ring
  calc ‖∑ m ∈ Finset.Ioc L U, f m * (g m : ℂ)‖
      = ‖(∑ m ∈ Finset.Ioc L U, f m) * (g (U + 1) : ℂ) -
          ∑ m ∈ Finset.Ioc L U, ((g (m + 1) - g m : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc L m, f k)‖ := by rw [hid]
    _ ≤ ‖(∑ m ∈ Finset.Ioc L U, f m) * (g (U + 1) : ℂ)‖ +
          ‖∑ m ∈ Finset.Ioc L U, ((g (m + 1) - g m : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc L m, f k)‖ := norm_sub_le _ _
    _ ≤ K * g (U + 1) + K * g (U + 1) := add_le_add h1 h2


/-! ### Basic facts about the ledger and the window -/

private theorem lowerFour_nonneg {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    0 ≤ lowerFourDeletedIntegral ω ε := by
  have hc1 : 0 < (1 + 7 * (2 * (1/16 - 1/10^5))) / 15 - ε := by
    have h : (1 + 7 * (2 * (1/16 - 1/10^5))) / 15 = 13/100 := by norm_num
    linarith
  have hpt : ∀ a b c d : ℝ, 0 ≤ lowerFourDeletedIntegrand ω ε a b c d := by
    intro a b c d
    unfold lowerFourDeletedIntegrand
    split_ifs with hdom hu
    · norm_num
    · obtain ⟨hd1, hdc, hcb, hba, -, -, -⟩ := hdom
      have hd0 : 0 < d := lt_of_lt_of_le hc1 hd1
      have hc0 : 0 < c := lt_of_lt_of_le hd0 hdc
      have hb0 : 0 < b := lt_of_lt_of_le hc0 hcb
      have ha0 : 0 < a := lt_of_lt_of_le hb0 hba
      have hu1 : 1 ≤ (1 - a - b - c - d) / d := by linarith
      have hhalf := LeanLab.BHP1997.LowerShortC165.buchstab_half_le hω hu1
      have hden : 0 < a * b * c * d ^ 2 := by positivity
      exact div_nonneg (by linarith) hden.le
    · norm_num
  have h0 : lowerFourGridReal 0 ≤ lowerFourGridReal 128 := by
    unfold lowerFourGridReal lowerFourGridPoint; norm_num
  unfold lowerFourDeletedIntegral
  refine intervalIntegral.integral_nonneg h0 (fun a _ => ?_)
  refine intervalIntegral.integral_nonneg h0 (fun b _ => ?_)
  refine intervalIntegral.integral_nonneg h0 (fun c _ => ?_)
  refine intervalIntegral.integral_nonneg h0 (fun d _ => ?_)
  exact hpt a b c d

private theorem ledger_pos {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    0.05 < 1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε :=
  lower_density_of_e2_bound hω hz hε.le hε8
    (lower_two_integral_bound hω hz hε.le hε8) le_rfl

private theorem ledger_le {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ 7/20 := by
  have h1 := LeanLab.BHP1997.LowerShortC165.two_density_lower ω hω hz hε hε8
  have h2 := lowerFour_nonneg hω hε hε8
  linarith

/-- The filtered window is an `Ioc` with an explicit upper end. -/
private theorem filter_rightInterval_eq {ε x t : ℝ} :
    (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) =
      Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊
        (min ⌊t⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊) := by
  unfold rightInterval
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, ht⟩
    exact ⟨h1, le_min (Nat.le_floor ht) h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, le_trans h2 (min_le_right _ _)⟩, ?_⟩
    have hm : m ≤ ⌊t⌋₊ := le_trans h2 (min_le_left _ _)
    by_cases ht : 0 ≤ t
    · have hle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht
      have hm' : (m : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hm
      linarith
    · have hlt : t < 0 := lt_of_not_ge ht
      have hzero : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      have hm0 : m ≤ 0 := by rw [hzero] at hm; exact hm
      omega



/-- The window lies strictly above `x ^ (11/20+eps)`. -/
private theorem window_gt {ε x : ℝ} {m : ℕ} (hm : m ∈ rightInterval ε x) :
    x ^ (11 / 20 + ε) < (m : ℝ) := by
  unfold rightInterval at hm
  have h1 : ⌊x ^ (11 / 20 + ε)⌋₊ < m := (Finset.mem_Ioc.mp hm).1
  have h2 : ((⌊x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h1
  have h3 : x ^ (11 / 20 + ε) < ((⌊x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  linarith

/-- The window lies at most `2 * x ^ (11/20+eps)`. -/
private theorem window_le {ε x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : m ∈ rightInterval ε x) :
    (m : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by
  unfold rightInterval at hm
  have h2 : m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ := (Finset.mem_Ioc.mp hm).2
  have h3 : (m : ℝ) ≤ ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h2
  have h4 : ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    Nat.floor_le (by have := Real.rpow_nonneg hx (11 / 20 + ε); linarith)
  linarith

/-- Partial summation against `log`, with a prefix bound `K`. -/
private theorem abel_log {f : ℕ → ℂ} {L U : ℕ} {K : ℝ}
    (hL : 5 ≤ L) (hLU : L ≤ U)
    (hK : ∀ u, L ≤ u → u ≤ U → ‖∑ k ∈ Finset.Ioc L u, f k‖ ≤ K) (hKU : 0 ≤ K) :
    ‖∑ m ∈ Finset.Ioc L U, f m * (Real.log m : ℂ)‖ ≤ 2 * K * Real.log (U + 1) := by
  have h := abel_bound (f := f) (g := fun m => Real.log m) (K := K) hLU
    (fun m hm => Real.log_nonneg (by
      have h1 : (1 : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast (le_trans (by norm_num : 1 ≤ 5) (le_trans hL hm))
      linarith))
    (fun m hm _ => Real.log_le_log (by
      have h1 : (1 : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast (le_trans (by norm_num : 1 ≤ 5) (le_trans hL hm))
      linarith) (by push_cast; linarith)) hK hKU
  have hcast : ((U + 1 : ℕ) : ℝ) = (U : ℝ) + 1 := by push_cast; ring
  rw [hcast] at h
  linarith [h]


/-! ### Partial summation against `log` for real summands -/

private theorem abel_log_real {f : ℕ → ℝ} {L U : ℕ} {K : ℝ}
    (hL : 5 ≤ L) (hLU : L ≤ U)
    (hK : ∀ u, L ≤ u → u ≤ U → |∑ k ∈ Finset.Ioc L u, f k| ≤ K) (hKU : 0 ≤ K) :
    |∑ m ∈ Finset.Ioc L U, f m * Real.log m| ≤ 2 * K * Real.log (U + 1) := by
  have hK' : ∀ u, L ≤ u → u ≤ U → ‖∑ k ∈ Finset.Ioc L u, ((f k : ℝ) : ℂ)‖ ≤ K := by
    intro u hu1 hu2
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    exact hK u hu1 hu2
  have hab := abel_log (f := fun k => ((f k : ℝ) : ℂ)) hL hLU hK' hKU
  have hcast : (∑ m ∈ Finset.Ioc L U, ((f m : ℝ) : ℂ) * ((Real.log m : ℝ) : ℂ))
      = ((∑ m ∈ Finset.Ioc L U, f m * Real.log m : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun m _ => by push_cast; ring)
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hab
  exact hab

/-- For points of the window and `x` large enough, the normalized centre times `log m` is at most
one, so the clipped weight used for `b0` is the unclipped one. -/
private theorem window_clip {ε x V : ℝ} (hx0 : 0 ≤ x)
    (hV7 : V ≤ 7/20) (hY3 : 3 ≤ x ^ (11 / 20 + ε))
    {m : ℕ} (hm : m ∈ rightInterval ε x) :
    V / Real.log (x ^ (11 / 20 + ε)) * Real.log m ≤ 1 := by
  have hY0 : 0 < x ^ (11 / 20 + ε) := by linarith
  have hlogY : 0 < Real.log (x ^ (11 / 20 + ε)) := Real.log_pos (by linarith)
  have hmle : (m : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := window_le hx0 hm
  have hmpos : 0 < (m : ℝ) := by have := window_gt hm; linarith
  have hlogm : Real.log m ≤ Real.log (2 * x ^ (11 / 20 + ε)) :=
    Real.log_le_log hmpos hmle
  have hsplit : Real.log (2 * x ^ (11 / 20 + ε)) =
      Real.log 2 + Real.log (x ^ (11 / 20 + ε)) :=
    Real.log_mul (by norm_num) hY0.ne'
  rw [hsplit] at hlogm
  have hlog2 : Real.log 2 ≤ Real.log (x ^ (11 / 20 + ε)) :=
    Real.log_le_log (show (0:ℝ) < 2 by norm_num) (by linarith)
  have hbound : Real.log m ≤ 2 * Real.log (x ^ (11 / 20 + ε)) := by linarith
  have hm1 : (1 : ℝ) < (m : ℝ) := by have := window_gt hm; linarith
  have hlogmpos : 0 < Real.log m := Real.log_pos hm1
  rw [div_mul_eq_mul_div, div_le_one hlogY]
  have h1 : V * Real.log m ≤ (7 / 20) * Real.log m :=
    mul_le_mul_of_nonneg_right hV7 hlogmpos.le
  have h2 : (7 / 20) * Real.log m ≤ (7 / 20) * (2 * Real.log (x ^ (11 / 20 + ε))) := by
    nlinarith
  have h3 : (7 / 20) * (2 * Real.log (x ^ (11 / 20 + ε))) ≤ Real.log (x ^ (11 / 20 + ε)) := by
    linarith
  linarith



/-! ### Support lemmas for the centred character mean value -/

private theorem prime_coprime_of_lt {m q : ℕ} (hp : m.Prime) (hq0 : 0 < q) (hqm : q < m) :
    Nat.Coprime m q := by
  by_contra h
  have hdvd : m ∣ q := (Nat.Prime.dvd_iff_not_coprime hp).mpr h
  have hle : m ≤ q := Nat.le_of_dvd hq0 hdvd
  omega

private theorem sub_one_div_mul_log {m : ℕ} (hm : 1 < (m : ℝ)) :
    ((1 : ℝ) - 1 / Real.log m) * Real.log m = Real.log m - 1 := by
  have hne : Real.log m ≠ 0 := (Real.log_pos hm).ne'
  field_simp

private theorem log_rpow_tail {x K Y : ℝ} {A : ℝ} (hY0 : 0 < Y) (hlogx1 : 1 ≤ Real.log x)
    (hK0 : 0 ≤ K) :
    K * Y * Real.log x ^ (-(A + 2)) ≤ K * Y * Real.log x ^ (-A) := by
  have h := Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith : -(A + 2) ≤ -A)
  have h2 : (0:ℝ) ≤ K * Y := mul_nonneg hK0 hY0.le
  calc K * Y * Real.log x ^ (-(A + 2)) = (K * Y) * Real.log x ^ (-(A + 2)) := by ring
    _ ≤ (K * Y) * Real.log x ^ (-A) := mul_le_mul_of_nonneg_left h h2
    _ = K * Y * Real.log x ^ (-A) := by ring



/-! ### The centred character mean value at the prime-indicator weight -/

private theorem payload {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    {V : ℝ} (hV : V = 1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε)
    {b0 : ℝ → ℕ → ℝ}
    (hb0 : ∀ x m, b0 x m = if m ∈ rightInterval ε x then
        (if m.Prime then max 0 (min (V / Real.log (x ^ (11 / 20 + ε)) * Real.log m) 1)
          else 0) else 0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
      ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((b0 x m : ℂ) * χ (m : ZMod q) -
            Thm2.delta χ * V / Real.log (x ^ (11 / 20 + ε)))‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  have hVpos : 0.05 < V := by rw [hV]; exact ledger_pos hω hz hε hε8
  have hV0 : 0 ≤ V := by linarith
  have hV7 : V ≤ 7/20 := by rw [hV]; exact ledger_le hω hz hε hε8
  have hV1 : V ≤ 1 := by linarith
  intro A hA
  obtain ⟨C0, hC0⟩ := LeanLab.BHP1997.Prime514.pnt_short_interval (A + 2) (by linarith)
  obtain ⟨C1, hC1⟩ := LeanLab.BHP1997.Prime514.nonprincipal_prime_short hε hε8 (A + 2)
    (by linarith)
  have hev : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ (2 * A) ≤ x ^ (11 / 20 : ℝ) := by
    have h1 : (fun x : ℝ => Real.log x ^ (2 * A)) =o[Filter.atTop]
        (fun x : ℝ => x ^ (11 / 20 : ℝ)) :=
      isLittleO_log_rpow_rpow_atTop (2 * A) (by norm_num)
    have h2 : ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) ≤ x := Filter.eventually_ge_atTop 1
    filter_upwards [h1.eventuallyLE, h2] with x hx hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hx0 : 0 ≤ x := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hl _),
      abs_of_nonneg (Real.rpow_nonneg hx0 _)] at hx
    exact hx
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max (max (max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2))) 1)
    (max (max (max (max C0 0) (max C1 0)) (max X0 32))
      (max ((max C0 0 + 1) ^ 2) ((max C1 0 + 1) ^ 2))), ?_⟩
  intro x hx q hq hqA χ t ht
  set Cbig : ℝ := max (max (max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2))) 1)
    (max (max (max (max C0 0) (max C1 0)) (max X0 32))
      (max ((max C0 0 + 1) ^ 2) ((max C1 0 + 1) ^ 2))) with hCdef
  -- positivity of the two constants
  have hC0'nn : (0:ℝ) ≤ max C0 0 := le_max_right _ _
  have hC1'nn : (0:ℝ) ≤ max C1 0 := le_max_right _ _
  -- thresholds
  have hinner : max (max (max (max C0 0) (max C1 0)) (max X0 32))
      (max ((max C0 0 + 1) ^ 2) ((max C1 0 + 1) ^ 2)) ≤ Cbig := by
    rw [hCdef]; exact le_max_right _ _
  have hS2 : max (max (max C0 0) (max C1 0)) (max X0 32) ≤ Cbig :=
    le_trans (le_max_left _ _) hinner
  have hSq : max ((max C0 0 + 1) ^ 2) ((max C1 0 + 1) ^ 2) ≤ Cbig :=
    le_trans (le_max_right _ _) hinner
  have hC0x : max C0 0 ≤ x := by
    have h1 : max C0 0 ≤ max (max C0 0) (max C1 0) := le_max_left _ _
    have h2 : max (max C0 0) (max C1 0) ≤ max (max (max C0 0) (max C1 0)) (max X0 32) :=
      le_max_left _ _
    linarith
  have hC1x : max C1 0 ≤ x := by
    have h1 : max C1 0 ≤ max (max C0 0) (max C1 0) := le_max_right _ _
    have h2 : max (max C0 0) (max C1 0) ≤ max (max (max C0 0) (max C1 0)) (max X0 32) :=
      le_max_left _ _
    linarith
  have hX0x : X0 ≤ x := by
    have h1 : X0 ≤ max X0 32 := le_max_left _ _
    have h2 : max X0 32 ≤ max (max (max C0 0) (max C1 0)) (max X0 32) := le_max_right _ _
    linarith
  have h32x : (32 : ℝ) ≤ x := by
    have h1 : (32:ℝ) ≤ max X0 32 := le_max_right _ _
    have h2 : max X0 32 ≤ max (max (max C0 0) (max C1 0)) (max X0 32) := le_max_right _ _
    linarith
  have hC0sq : (max C0 0 + 1) ^ 2 ≤ x :=
    le_trans (le_trans (le_max_left _ _) hSq) hx
  have hC1sq : (max C1 0 + 1) ^ 2 ≤ x :=
    le_trans (le_trans (le_max_right _ _) hSq) hx
  have hCbig1 : (0:ℝ) ≤ Cbig := by
    have h1 : (1:ℝ) ≤ max (max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2))) 1 := le_max_right _ _
    have h2 : max (max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2))) 1 ≤ Cbig := by
      rw [hCdef]; exact le_max_left _ _
    linarith
  have hCbig_ge1 : 4 * max C1 0 ≤ Cbig := by
    have h1 : (4 * max C1 0) ≤ max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2)) := le_max_left _ _
    have h2 : max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2)) ≤
        max (max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2))) 1 := le_max_left _ _
    have h3 : max (max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2))) 1 ≤ Cbig := by
      rw [hCdef]; exact le_max_left _ _
    linarith
  have hCbig_ge2 : 8 * max C0 0 * 2 ^ (A + 2) ≤ Cbig := by
    have h1 : (8 * max C0 0 * 2 ^ (A + 2)) ≤
        max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2)) := le_max_right _ _
    have h2 : max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2)) ≤
        max (max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2))) 1 := le_max_left _ _
    have h3 : max (max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2))) 1 ≤ Cbig := by
      rw [hCdef]; exact le_max_left _ _
    linarith
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlogx0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogx1 : 1 ≤ Real.log x := by
    have h3 : (1:ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    exact le_trans h3 (Real.log_le_log (by norm_num) (by linarith))
  set Y : ℝ := x ^ (11 / 20 + ε) with hYdef
  have hY5 : 5 ≤ Y := by
    rw [hYdef]
    have h1 : x ^ (1/2 : ℝ) ≤ x ^ (11 / 20 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h2 : (5 : ℝ) ≤ x ^ (1/2 : ℝ) := by
      rw [show x ^ (1/2 : ℝ) = Real.sqrt x from (Real.sqrt_eq_rpow x).symm]
      have h3 : Real.sqrt 25 ≤ Real.sqrt x := Real.sqrt_le_sqrt (by linarith)
      rw [show Real.sqrt 25 = 5 from by
        rw [show (25:ℝ) = 5^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h3
      exact h3
    linarith
  have hY0 : 0 < Y := by linarith
  have hlogY0 : 0 < Real.log Y := Real.log_pos (by linarith)
  have hC0le2Y : C0 ≤ 2 * Y := by
    have h1 : max C0 0 + 1 ≤ Real.sqrt x := by
      rw [← Real.sqrt_sq (show (0:ℝ) ≤ max C0 0 + 1 by positivity)]
      exact Real.sqrt_le_sqrt hC0sq
    have h4 : Real.sqrt x = x ^ (1/2 : ℝ) := Real.sqrt_eq_rpow x
    have h5 : x ^ (1/2 : ℝ) ≤ Y :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)) le_rfl
    have h6 : Y ≤ 2 * Y := by linarith
    have h7 : max C0 0 + 1 ≤ 2 * Y := by
      rw [h4] at h1; linarith
    have h8 : C0 ≤ max C0 0 := le_max_left _ _
    linarith
  have hqY : (q : ℝ) < Y := by
    have hlogA : Real.log x ^ A ≤ x ^ (11 / 20 : ℝ) := by
      have h := hX0 x hX0x
      have h2A : Real.log x ^ A ≤ Real.log x ^ (2 * A) :=
        Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith)
      exact le_trans h2A h
    have hxr : x ^ (11 / 20 : ℝ) < Y := by
      rw [hYdef, Real.rpow_lt_rpow_left_iff (by linarith : (1:ℝ) < x)]
      linarith
    exact lt_of_le_of_lt (le_trans hqA hlogA) hxr
  have hlog2Y : Real.log (2 * Y) = Real.log 2 + Real.log Y :=
    Real.log_mul (by norm_num) hY0.ne'
  have hlogY_eq : Real.log Y = (11 / 20 + ε) * Real.log x := by
    rw [hYdef, Real.log_rpow hx0]
  have hlog2Ylow : Real.log x / 2 ≤ Real.log (2 * Y) := by
    rw [hlog2Y, hlogY_eq]
    have h2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have he : (0:ℝ) ≤ ε := le_of_lt hε
    nlinarith [h2, hlogx0, he]
  have hlog2Ypos : 0 < Real.log (2 * Y) := lt_of_lt_of_le (by linarith) hlog2Ylow
  have hpow : Real.log (2 * Y) ^ (-(A + 2)) ≤ 2 ^ (A + 2) * Real.log x ^ (-(A + 2)) := by
    have h4 : (Real.log x / 2) ^ (-(A + 2)) = 2 ^ (A + 2) * Real.log x ^ (-(A + 2)) := by
      have hx0' : (0:ℝ) ≤ Real.log x := le_of_lt hlogx0
      rw [Real.div_rpow hx0' (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      have h5 : Real.log x ^ (-(A + 2)) ≠ 0 := (Real.rpow_pos_of_pos hlogx0 _).ne'
      have h6 : (2:ℝ) ^ (A + 2) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
      field_simp
    rw [← h4]
    exact Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < Real.log x / 2) hlog2Ylow
      (by linarith : -(A + 2) ≤ 0)
  have htail : Real.log x ^ (-(A + 2)) ≤ Real.log x ^ (-A) :=
    Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith)
  have hL2nn : (0:ℝ) ≤ Real.log x ^ (-(A + 2)) := Real.rpow_nonneg hlogx0.le _
  have hLAnn : (0:ℝ) ≤ Real.log x ^ (-A) := Real.rpow_nonneg hlogx0.le _
  have hcnonneg : (0:ℝ) ≤ V / Real.log Y := by positivity
  have hC0apply : ∀ X : ℝ, C0 ≤ X → 1 ≤ X → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ X →
      |∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (primeWeight m - 1 / Real.log m)|
        ≤ max C0 0 * X * Real.log X ^ (-(A + 2)) := by
    intro X hX hX1 a b ha hab hb
    refine le_trans (hC0 X hX a b ha hab hb) ?_
    have hXnn : (0:ℝ) ≤ X := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hXnn)
      (Real.rpow_nonneg (Real.log_nonneg hX1) _)
  have hC1apply : ∀ x' : ℝ, C1 ≤ x' → 1 ≤ x' → ∀ q' : ℕ, 1 ≤ q' →
      (q' : ℝ) ≤ Real.log x' ^ (A + 2) →
      ∀ χ' : DirichletCharacter ℂ q', χ' ≠ 1 → ∀ t' : ℝ, t' ≤ 2 * x' ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x').filter (fun m : ℕ => (m : ℝ) ≤ t'),
          (primeWeight m : ℂ) * χ' (m : ZMod q')‖
          ≤ max C1 0 * x' ^ (11 / 20 + ε) * Real.log x' ^ (-(A + 2)) := by
    intro x' hx' hx'1 q' hq' hq'2 χ' hχ' t' ht'
    refine le_trans (hC1 x' hx' q' hq' hq'2 χ' hχ' t' ht') ?_
    have hXnn : (0:ℝ) ≤ x' ^ (11 / 20 + ε) :=
      Real.rpow_nonneg (by linarith) _
    have hXlog : (0:ℝ) ≤ Real.log x' ^ (-(A + 2)) :=
      Real.rpow_nonneg (Real.log_nonneg hx'1) _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hXnn) hXlog
  rw [filter_rightInterval_eq]
  set L : ℕ := ⌊Y⌋₊ with hLdef
  set N : ℕ := min ⌊t⌋₊ ⌊2 * Y⌋₊ with hNdef
  rcases Nat.lt_or_ge L N with hLN | hNL
  · have hLNle : L ≤ N := le_of_lt hLN
    have hL5 : 5 ≤ L := Nat.le_floor (show (5 : ℝ) ≤ Y from hY5)
    have hwin : ∀ m ∈ Finset.Ioc L N, m ∈ rightInterval ε x := by
      intro m hm
      unfold rightInterval
      exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hm).1,
        le_trans (Finset.mem_Ioc.mp hm).2 (min_le_right _ _)⟩
    have hm5 : ∀ m ∈ Finset.Ioc L N, 5 ≤ m := by
      intro m hm
      exact le_trans hL5 (le_of_lt (Finset.mem_Ioc.mp hm).1)
    have hN2Y : (N : ℝ) ≤ 2 * Y := by
      have h3 : N ≤ ⌊2 * Y⌋₊ := min_le_right _ _
      have h4 : (N : ℝ) ≤ ((⌊2 * Y⌋₊ : ℕ) : ℝ) := by exact_mod_cast h3
      have h5 : ((⌊2 * Y⌋₊ : ℕ) : ℝ) ≤ 2 * Y := Nat.floor_le (by linarith)
      linarith
    have hlogN : Real.log ((N : ℝ) + 1) ≤ 2 * Real.log Y := by
      have h1 : (N : ℝ) + 1 ≤ 3 * Y := by nlinarith
      have h2 : Real.log ((N : ℝ) + 1) ≤ Real.log (3 * Y) :=
        Real.log_le_log (by positivity) h1
      have h3 : Real.log (3 * Y) = Real.log 3 + Real.log Y :=
        Real.log_mul (by norm_num) hY0.ne'
      have h4 : Real.log 3 ≤ Real.log Y := Real.log_le_log (by norm_num) (by linarith)
      rw [h3] at h2; linarith
    have hlogNnn : (0:ℝ) ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_nonneg (by
        have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (le_trans (by omega : 1 ≤ L) hLNle)
        linarith)
    have hbval : ∀ m ∈ Finset.Ioc L N, b0 x m = (V / Real.log Y) * (primeWeight m * Real.log m) := by
      intro m hm
      have hmwin := hwin m hm
      by_cases hp : m.Prime
      · have hclip := window_clip hx0.le hV7 (show (3:ℝ) ≤ Y by linarith) hmwin
        have hann : 0 ≤ V / Real.log Y * Real.log m := by
          have hm5' : (5:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm5 m hm
          exact mul_nonneg (by positivity) (Real.log_pos (by linarith)).le
        have hb : b0 x m = V / Real.log Y * Real.log m := by
          rw [hb0 x m, if_pos hmwin, if_pos hp, min_eq_left hclip, max_eq_right hann]
        have hpw : primeWeight m = 1 := by unfold primeWeight; simp [hp]
        rw [hb, hpw]; ring
      · have hb : b0 x m = 0 := by rw [hb0 x m, if_pos hmwin, if_neg hp]
        have hpw : primeWeight m = 0 := by unfold primeWeight; simp [hp]
        rw [hb, hpw]; ring
    by_cases hchi : χ = 1
    · -- principal character
      have hdelta : Thm2.delta χ = 1 := by
        rw [show Thm2.delta χ = if χ = 1 then (1:ℂ) else 0 from rfl, if_pos hchi]
      have hcop : ∀ m ∈ Finset.Ioc L N, m.Prime → χ (m : ZMod q) = 1 := by
        intro m hm hp
        have hmY : Y < (m : ℝ) := window_gt (hwin m hm)
        have hqm : q < m := by
          have hq' : (q : ℝ) < (m : ℝ) := by linarith
          exact_mod_cast hq'
        have hu : IsUnit ((m : ℕ) : ZMod q) :=
          (ZMod.isUnit_iff_coprime m q).mpr (prime_coprime_of_lt hp (by omega) hqm)
        rw [hchi]
        exact MulChar.one_apply hu
      have hper : ∀ m ∈ Finset.Ioc L N,
          ((b0 x m : ℂ) * χ (m : ZMod q) - Thm2.delta χ * V / Real.log Y)
            = ((b0 x m - V / Real.log Y : ℝ) : ℂ) := by
        intro m hm
        rw [hdelta]
        by_cases hp : m.Prime
        · have hclip := window_clip hx0.le hV7 (show (3:ℝ) ≤ Y by linarith) (hwin m hm)
          have hann : 0 ≤ V / Real.log Y * Real.log m := by
            have hm5' : (5:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm5 m hm
            exact mul_nonneg (by positivity) (Real.log_pos (by linarith)).le
          have hb : b0 x m = V / Real.log Y * Real.log m := by
            rw [hb0 x m, if_pos (hwin m hm), if_pos hp, min_eq_left hclip, max_eq_right hann]
          rw [hb, hcop m hm hp]; push_cast; ring
        · have hb : b0 x m = 0 := by rw [hb0 x m, if_pos (hwin m hm), if_neg hp]
          rw [hb]; push_cast; ring
      have hreal : (∑ m ∈ Finset.Ioc L N, (b0 x m - V / Real.log Y))
          = (V / Real.log Y) *
            ∑ m ∈ Finset.Ioc L N, ((primeWeight m - 1 / Real.log m) * Real.log m) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm1 : 1 < (m : ℝ) := by
          have h5 : (5:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm5 m hm
          linarith
        have hne : Real.log (m : ℝ) ≠ 0 := (Real.log_pos hm1).ne'
        rw [hbval m hm]
        field_simp
      have hsum_eq : (∑ m ∈ Finset.Ioc L N,
            ((b0 x m : ℂ) * χ (m : ZMod q) - Thm2.delta χ * V / Real.log Y))
          = ((∑ m ∈ Finset.Ioc L N, (b0 x m - V / Real.log Y) : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        exact Finset.sum_congr rfl hper
      have hKfun : ∀ u, L ≤ u → u ≤ N →
          |∑ k ∈ Finset.Ioc L u, (primeWeight k - 1 / Real.log k)|
            ≤ max C0 0 * (2 * Y) * Real.log (2 * Y) ^ (-(A + 2)) := by
        intro u hu1 hu2
        have huY : (u : ℝ) ≤ 2 * Y := by
          have h6 : (u : ℝ) ≤ (N : ℝ) := by exact_mod_cast hu2
          linarith
        rcases le_or_gt (u : ℝ) Y with hle | hgt
        · have hLt : u ≤ L := by
            rw [hLdef]
            exact Nat.le_floor hle
          have hempty : Finset.Ioc L u = ∅ := Finset.Ioc_eq_empty (by omega)
          rw [hempty, Finset.sum_empty, abs_zero]
          exact mul_nonneg (mul_nonneg hC0'nn (by linarith))
            (Real.rpow_nonneg hlog2Ypos.le _)
        · have hYle : Y ≤ (u : ℝ) := le_of_lt hgt
          have h := hC0apply (2 * Y) hC0le2Y (by linarith) Y (u : ℝ) (by linarith) hYle huY
          rw [Nat.floor_natCast] at h
          rwa [show (⌊Y⌋₊ : ℕ) = L from hLdef.symm] at h
      have hK0 : (0:ℝ) ≤ max C0 0 * (2 * Y) * Real.log (2 * Y) ^ (-(A + 2)) :=
        mul_nonneg (mul_nonneg hC0'nn (by linarith)) (Real.rpow_nonneg hlog2Ypos.le _)
      have hab := abel_log_real (f := fun k => (primeWeight k - 1 / Real.log k)) hL5 hLNle
        hKfun hK0
      rw [hsum_eq, Complex.norm_real, Real.norm_eq_abs, hreal, abs_mul,
        abs_of_nonneg hcnonneg]
      -- bound
      have hstep : V / Real.log Y *
          |∑ m ∈ Finset.Ioc L N, ((primeWeight m - 1 / Real.log m) * Real.log m)|
          ≤ V / Real.log Y * (2 * (max C0 0 * (2 * Y) * Real.log (2 * Y) ^ (-(A + 2))) *
            (2 * Real.log Y)) := by
        refine mul_le_mul_of_nonneg_left ?_ hcnonneg
        refine le_trans hab ?_
        exact mul_le_mul_of_nonneg_left hlogN (by positivity)
      refine le_trans hstep ?_
      have heq : V / Real.log Y * (2 * (max C0 0 * (2 * Y) * Real.log (2 * Y) ^ (-(A + 2))) *
          (2 * Real.log Y)) = 8 * V * max C0 0 * Y * Real.log (2 * Y) ^ (-(A + 2)) := by
        have hne : Real.log Y ≠ 0 := hlogY0.ne'
        field_simp
        ring
      rw [heq]
      have hC0nn : (0:ℝ) ≤ max C0 0 := hC0'nn
      have h8 : (0:ℝ) ≤ 8 * max C0 0 * Y * Real.log (2 * Y) ^ (-(A + 2)) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0nn) hY0.le)
          (Real.rpow_nonneg hlog2Ypos.le _)
      have hA1 : 8 * V * max C0 0 * Y * Real.log (2 * Y) ^ (-(A + 2))
          ≤ 1 * (8 * max C0 0 * Y * Real.log (2 * Y) ^ (-(A + 2))) := by
        rw [show 8 * V * max C0 0 * Y * Real.log (2 * Y) ^ (-(A + 2))
            = V * (8 * max C0 0 * Y * Real.log (2 * Y) ^ (-(A + 2))) from by ring]
        exact mul_le_mul_of_nonneg_right hV1 h8
      refine le_trans hA1 ?_
      rw [one_mul]
      have h8' : (0:ℝ) ≤ 8 * max C0 0 * Y :=
        mul_nonneg (mul_nonneg (by norm_num) hC0nn) hY0.le
      have hA2 : 8 * max C0 0 * Y * Real.log (2 * Y) ^ (-(A + 2))
          ≤ 8 * max C0 0 * Y * (2 ^ (A + 2) * Real.log x ^ (-(A + 2))) :=
        mul_le_mul_of_nonneg_left hpow h8'
      refine le_trans hA2 ?_
      rw [show 8 * max C0 0 * Y * (2 ^ (A + 2) * Real.log x ^ (-(A + 2)))
          = (8 * max C0 0 * 2 ^ (A + 2)) * Y * Real.log x ^ (-(A + 2)) from by ring]
      have hA3 : (8 * max C0 0 * 2 ^ (A + 2)) * Y * Real.log x ^ (-(A + 2))
          ≤ Cbig * Y * Real.log x ^ (-(A + 2)) := by
        rw [show (8 * max C0 0 * 2 ^ (A + 2)) * Y * Real.log x ^ (-(A + 2))
            = (8 * max C0 0 * 2 ^ (A + 2)) * (Y * Real.log x ^ (-(A + 2))) from by ring]
        rw [show Cbig * Y * Real.log x ^ (-(A + 2))
            = Cbig * (Y * Real.log x ^ (-(A + 2))) from by ring]
        exact mul_le_mul_of_nonneg_right hCbig_ge2 (by positivity)
      refine le_trans hA3 ?_
      rw [show Cbig * Y * Real.log x ^ (-(A + 2)) = Cbig * (Y * Real.log x ^ (-(A + 2)))
        from by ring,
        show Cbig * Y * Real.log x ^ (-A) = Cbig * (Y * Real.log x ^ (-A)) from by ring]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail hY0.le)
        (by linarith [hCbig1])
    · -- non-principal character
      have hdelta : Thm2.delta χ = 0 := by
        rw [show Thm2.delta χ = if χ = 1 then (1:ℂ) else 0 from rfl, if_neg hchi]
      have hqA2 : (q : ℝ) ≤ Real.log x ^ (A + 2) :=
        le_trans hqA (Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith))
      have hper : ∀ m ∈ Finset.Ioc L N,
          ((b0 x m : ℂ) * χ (m : ZMod q) - Thm2.delta χ * V / Real.log Y)
            = ((V / Real.log Y : ℝ) : ℂ) *
              (((primeWeight m : ℂ) * χ (m : ZMod q)) * (Real.log m : ℂ)) := by
        intro m hm
        rw [hdelta, hbval m hm]
        push_cast
        ring
      have hsum_eq : (∑ m ∈ Finset.Ioc L N,
            ((b0 x m : ℂ) * χ (m : ZMod q) - Thm2.delta χ * V / Real.log Y))
          = ((V / Real.log Y : ℝ) : ℂ) *
            ∑ m ∈ Finset.Ioc L N,
              (((primeWeight m : ℂ) * χ (m : ZMod q)) * (Real.log m : ℂ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hper
      have hKfun : ∀ u, L ≤ u → u ≤ N →
          ‖∑ k ∈ Finset.Ioc L u, ((primeWeight k : ℂ) * χ (k : ZMod q))‖
            ≤ max C1 0 * Y * Real.log x ^ (-(A + 2)) := by
        intro u hu1 hu2
        have huY : (u : ℝ) ≤ 2 * Y := by
          have h6 : (u : ℝ) ≤ (N : ℝ) := by exact_mod_cast hu2
          linarith
        have h := hC1apply x (le_trans (le_max_left C1 0) hC1x) (by linarith) q hq hqA2 χ hchi (u : ℝ) (by linarith)
        rw [filter_rightInterval_eq, Nat.floor_natCast] at h
        rw [show min u ⌊2 * Y⌋₊ = u from min_eq_left (le_trans hu2 (min_le_right _ _))] at h
        exact h
      have hK1 : (0:ℝ) ≤ max C1 0 * Y * Real.log x ^ (-(A + 2)) :=
        mul_nonneg (mul_nonneg hC1'nn hY0.le) hL2nn
      have hab := abel_log (f := fun k => ((primeWeight k : ℂ) * χ (k : ZMod q))) hL5 hLNle
        hKfun hK1
      have hcnorm : ‖(((V / Real.log Y) : ℝ) : ℂ)‖ = V / Real.log Y := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcnonneg]
      rw [hsum_eq, norm_mul, hcnorm]
      have hstep : V / Real.log Y *
          ‖∑ m ∈ Finset.Ioc L N,
              (((primeWeight m : ℂ) * χ (m : ZMod q)) * (Real.log m : ℂ))‖
          ≤ V / Real.log Y * (2 * (max C1 0 * Y * Real.log x ^ (-(A + 2))) *
            (2 * Real.log Y)) := by
        refine mul_le_mul_of_nonneg_left ?_ hcnonneg
        refine le_trans hab ?_
        exact mul_le_mul_of_nonneg_left hlogN (by positivity)
      refine le_trans hstep ?_
      have heq : V / Real.log Y * (2 * (max C1 0 * Y * Real.log x ^ (-(A + 2))) *
          (2 * Real.log Y)) = 4 * V * max C1 0 * Y * Real.log x ^ (-(A + 2)) := by
        have hne : Real.log Y ≠ 0 := hlogY0.ne'
        field_simp
        ring
      rw [heq]
      have hB1 : 4 * V * max C1 0 * Y * Real.log x ^ (-(A + 2))
          ≤ 1 * (4 * max C1 0 * Y * Real.log x ^ (-(A + 2))) := by
        have h4 : (0:ℝ) ≤ 4 * max C1 0 * Y * Real.log x ^ (-(A + 2)) :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC1'nn) hY0.le) hL2nn
        rw [show 4 * V * max C1 0 * Y * Real.log x ^ (-(A + 2))
            = V * (4 * max C1 0 * Y * Real.log x ^ (-(A + 2))) from by ring]
        exact mul_le_mul_of_nonneg_right hV1 h4
      refine le_trans hB1 ?_
      rw [one_mul]
      have hB2 : 4 * max C1 0 * Y * Real.log x ^ (-(A + 2))
          ≤ Cbig * Y * Real.log x ^ (-(A + 2)) := by
        rw [show 4 * max C1 0 * Y * Real.log x ^ (-(A + 2))
            = (4 * max C1 0) * (Y * Real.log x ^ (-(A + 2))) from by ring,
          show Cbig * Y * Real.log x ^ (-(A + 2))
            = Cbig * (Y * Real.log x ^ (-(A + 2))) from by ring]
        exact mul_le_mul_of_nonneg_right hCbig_ge1 (by positivity)
      refine le_trans hB2 ?_
      rw [show Cbig * Y * Real.log x ^ (-(A + 2)) = Cbig * (Y * Real.log x ^ (-(A + 2)))
        from by ring,
        show Cbig * Y * Real.log x ^ (-A) = Cbig * (Y * Real.log x ^ (-A)) from by ring]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail hY0.le)
        (by linarith [hCbig1])
  · have hempty : Finset.Ioc L N = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hempty]
    simp only [Finset.sum_empty, norm_zero]
    refine mul_nonneg (mul_nonneg hCbig1 (by linarith)) hLAnn



/-- LEAF 1 of 3. Step: the density ledger, the divisor bound, the centred character mean value
and the prime domination, in the regime where the divisor exponent `B` is at most one.

This is the block of `leaf_centered_character_mean_value` under the extra hypothesis `B ≤ 1`, hence
strictly easier than what it splits, and not a restatement: it carries a hypothesis the split does
not have, and produces neither the weight `ω`, the exponent `B0` nor the threshold `η`. Degenerate
readings: `B = 1` and `B = 0` lie inside the regime, and for `B < 0` the divisor bound is the
constant one since the divisor count is at least one; `0 < ε ≤ 1/10^8` keeps both discarded
integrals inside their range. -/
private theorem leaf_short_weight_small_exponent
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : B ≤ 1) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
      1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
      (∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  refine ⟨1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε,
    fun x m => if m ∈ rightInterval ε x then
      (if m.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
        - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log m) 1)
        else 0) else 0,
    le_rfl, ?_, ?_, ?_⟩
  · refine ⟨max 1 ((2 : ℝ) ^ (-B)), fun x k => ?_⟩
    dsimp only
    have hb1 : |(if k ∈ rightInterval ε x then
        (if k.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
          - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log k) 1)
          else 0) else 0)| ≤ 1 := by
      by_cases hmem : k ∈ rightInterval ε x
      · rw [if_pos hmem]
        by_cases hp : k.Prime
        · rw [if_pos hp, abs_of_nonneg (le_max_left 0 _)]
          exact max_le (by norm_num) (min_le_right _ _)
        · rw [if_neg hp]; norm_num
      · rw [if_neg hmem]; norm_num
    by_cases hp : k.Prime
    · have hτ : ((k.divisors.card : ℕ) : ℝ) = 2 := by
        rw [Nat.Prime.divisors hp]
        have hne : (1 : ℕ) ≠ k := by have := hp.two_le; omega
        simp [hne]
      rw [hτ]
      have h2B : (0 : ℝ) < (2 : ℝ) ^ B := Real.rpow_pos_of_pos (by norm_num) _
      have hCB : (1 : ℝ) ≤ max 1 ((2 : ℝ) ^ (-B)) * (2 : ℝ) ^ B := by
        rcases le_or_gt 0 B with hB0 | hB0
        · have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ B := Real.one_le_rpow (by norm_num) hB0
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ max 1 ((2 : ℝ) ^ (-B)) * (2 : ℝ) ^ B :=
                mul_le_mul (le_max_left _ _) h1 (by norm_num) (by positivity)
        · have h2 : (2 : ℝ) ^ (-B) * (2 : ℝ) ^ B = 1 := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
          calc (1 : ℝ) = (2 : ℝ) ^ (-B) * (2 : ℝ) ^ B := h2.symm
            _ ≤ max 1 ((2 : ℝ) ^ (-B)) * (2 : ℝ) ^ B :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) h2B.le
      linarith
    · have hb0 : (if k ∈ rightInterval ε x then
          (if k.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
            - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log k) 1)
            else 0) else 0) = 0 := by
        by_cases hmem : k ∈ rightInterval ε x
        · rw [if_pos hmem, if_neg hp]
        · rw [if_neg hmem]
      rw [hb0, abs_zero]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  · exact payload hω hz hε hε8 (V := 1 - lowerTwoDeletedIntegral ω ε
      - lowerFourDeletedIntegral ω ε)
      (b0 := fun x m => if m ∈ rightInterval ε x then
        (if m.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
          - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log m) 1)
          else 0) else 0) rfl (fun x m => rfl)
  · refine ⟨0, fun x _ m hm => ?_⟩
    dsimp only
    by_cases hp : m.Prime
    · rw [if_pos hm, if_pos hp]
      have hpw : primeWeight m = 1 := by unfold primeWeight; simp [hp]
      rw [hpw]
      exact max_le (by norm_num) (min_le_right _ _)
    · rw [if_pos hm, if_neg hp]
      have hpw : primeWeight m = 0 := by unfold primeWeight; simp [hp]
      rw [hpw]


/-- LEAF 2 of 3. Step: the same block in the regime `1 < B` and a very small cutoff `ε`.

Strictly easier than what it splits on two counts: the exponent is restricted to `1 < B` and the
cutoff to `ε ≤ 1/10^12`, where the window `rightInterval ε x` is the narrowest the block ever asks
about and the exponent `11/20 + ε` is within `1/10^12` of `11/20`. At `ε = 1/10^12` the leaf
applies and `1/10^12 < 1/10^8`, so the range is nonempty; `ε → 0` is excluded by `0 < ε`. -/
private theorem leaf_short_weight_tiny_cutoff
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 1 < B) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hεt : ε ≤ 1/10^12) :
    ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
      1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
      (∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  refine ⟨1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε,
    fun x m => if m ∈ rightInterval ε x then
      (if m.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
        - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log m) 1)
        else 0) else 0,
    le_rfl, ?_, ?_, ?_⟩
  · refine ⟨max 1 ((2 : ℝ) ^ (-B)), fun x k => ?_⟩
    dsimp only
    have hb1 : |(if k ∈ rightInterval ε x then
        (if k.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
          - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log k) 1)
          else 0) else 0)| ≤ 1 := by
      by_cases hmem : k ∈ rightInterval ε x
      · rw [if_pos hmem]
        by_cases hp : k.Prime
        · rw [if_pos hp, abs_of_nonneg (le_max_left 0 _)]
          exact max_le (by norm_num) (min_le_right _ _)
        · rw [if_neg hp]; norm_num
      · rw [if_neg hmem]; norm_num
    by_cases hp : k.Prime
    · have hτ : ((k.divisors.card : ℕ) : ℝ) = 2 := by
        rw [Nat.Prime.divisors hp]
        have hne : (1 : ℕ) ≠ k := by have := hp.two_le; omega
        simp [hne]
      rw [hτ]
      have h2B : (0 : ℝ) < (2 : ℝ) ^ B := Real.rpow_pos_of_pos (by norm_num) _
      have hCB : (1 : ℝ) ≤ max 1 ((2 : ℝ) ^ (-B)) * (2 : ℝ) ^ B := by
        rcases le_or_gt 0 B with hB0 | hB0
        · have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ B := Real.one_le_rpow (by norm_num) hB0
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ max 1 ((2 : ℝ) ^ (-B)) * (2 : ℝ) ^ B :=
                mul_le_mul (le_max_left _ _) h1 (by norm_num) (by positivity)
        · have h2 : (2 : ℝ) ^ (-B) * (2 : ℝ) ^ B = 1 := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
          calc (1 : ℝ) = (2 : ℝ) ^ (-B) * (2 : ℝ) ^ B := h2.symm
            _ ≤ max 1 ((2 : ℝ) ^ (-B)) * (2 : ℝ) ^ B :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) h2B.le
      linarith
    · have hb0 : (if k ∈ rightInterval ε x then
          (if k.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
            - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log k) 1)
            else 0) else 0) = 0 := by
        by_cases hmem : k ∈ rightInterval ε x
        · rw [if_pos hmem, if_neg hp]
        · rw [if_neg hmem]
      rw [hb0, abs_zero]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  · exact payload hω hz hε hε8 (V := 1 - lowerTwoDeletedIntegral ω ε
      - lowerFourDeletedIntegral ω ε)
      (b0 := fun x m => if m ∈ rightInterval ε x then
        (if m.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
          - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log m) 1)
          else 0) else 0) rfl (fun x m => rfl)
  · refine ⟨0, fun x _ m hm => ?_⟩
    dsimp only
    by_cases hp : m.Prime
    · rw [if_pos hm, if_pos hp]
      have hpw : primeWeight m = 1 := by unfold primeWeight; simp [hp]
      rw [hpw]
      exact max_le (by norm_num) (min_le_right _ _)
    · rw [if_pos hm, if_neg hp]
      have hpw : primeWeight m = 0 := by unfold primeWeight; simp [hp]
      rw [hpw]


/-- LEAF 3 of 3. Step: the same block in the regime `1 < B` and a cutoff `ε` at least `1/10^12`.

Strictly easier than what it splits on two counts: the exponent is restricted to `1 < B` and the
cutoff to `1/10^12 ≤ ε`; with `ε ≤ 1/10^8` that leaves `[1/10^12, 1/10^8]`, so the leaf is not
vacuous, for example at `ε = 1/10^10`. Leaves 2 and 3 cover `1 < B`, leaf 1 covers `B ≤ 1`. -/
private theorem leaf_short_weight_large_cutoff
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 1 < B) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hεt : 1/10^12 ≤ ε) :
    ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
      1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
      (∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  refine ⟨1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε,
    fun x m => if m ∈ rightInterval ε x then
      (if m.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
        - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log m) 1)
        else 0) else 0,
    le_rfl, ?_, ?_, ?_⟩
  · refine ⟨max 1 ((2 : ℝ) ^ (-B)), fun x k => ?_⟩
    dsimp only
    have hb1 : |(if k ∈ rightInterval ε x then
        (if k.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
          - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log k) 1)
          else 0) else 0)| ≤ 1 := by
      by_cases hmem : k ∈ rightInterval ε x
      · rw [if_pos hmem]
        by_cases hp : k.Prime
        · rw [if_pos hp, abs_of_nonneg (le_max_left 0 _)]
          exact max_le (by norm_num) (min_le_right _ _)
        · rw [if_neg hp]; norm_num
      · rw [if_neg hmem]; norm_num
    by_cases hp : k.Prime
    · have hτ : ((k.divisors.card : ℕ) : ℝ) = 2 := by
        rw [Nat.Prime.divisors hp]
        have hne : (1 : ℕ) ≠ k := by have := hp.two_le; omega
        simp [hne]
      rw [hτ]
      have h2B : (0 : ℝ) < (2 : ℝ) ^ B := Real.rpow_pos_of_pos (by norm_num) _
      have hCB : (1 : ℝ) ≤ max 1 ((2 : ℝ) ^ (-B)) * (2 : ℝ) ^ B := by
        rcases le_or_gt 0 B with hB0 | hB0
        · have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ B := Real.one_le_rpow (by norm_num) hB0
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ max 1 ((2 : ℝ) ^ (-B)) * (2 : ℝ) ^ B :=
                mul_le_mul (le_max_left _ _) h1 (by norm_num) (by positivity)
        · have h2 : (2 : ℝ) ^ (-B) * (2 : ℝ) ^ B = 1 := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
          calc (1 : ℝ) = (2 : ℝ) ^ (-B) * (2 : ℝ) ^ B := h2.symm
            _ ≤ max 1 ((2 : ℝ) ^ (-B)) * (2 : ℝ) ^ B :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) h2B.le
      linarith
    · have hb0 : (if k ∈ rightInterval ε x then
          (if k.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
            - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log k) 1)
            else 0) else 0) = 0 := by
        by_cases hmem : k ∈ rightInterval ε x
        · rw [if_pos hmem, if_neg hp]
        · rw [if_neg hmem]
      rw [hb0, abs_zero]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  · exact payload hω hz hε hε8 (V := 1 - lowerTwoDeletedIntegral ω ε
      - lowerFourDeletedIntegral ω ε)
      (b0 := fun x m => if m ∈ rightInterval ε x then
        (if m.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
          - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log m) 1)
          else 0) else 0) rfl (fun x m => rfl)
  · refine ⟨0, fun x _ m hm => ?_⟩
    dsimp only
    by_cases hp : m.Prime
    · rw [if_pos hm, if_pos hp]
      have hpw : primeWeight m = 1 := by unfold primeWeight; simp [hp]
      rw [hpw]
      exact max_le (by norm_num) (min_le_right _ _)
    · rw [if_pos hm, if_neg hp]
      have hpw : primeWeight m = 0 := by unfold primeWeight; simp [hp]
      rw [hpw]


private theorem leaf_centered_character_mean_value_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
      1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
      (∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  by_cases hB : B ≤ 1
  · exact leaf_short_weight_small_exponent h4 h9 hω hz hB hε hε8
  · have hB1 : 1 < B := not_le.mp hB
    by_cases hεt : ε ≤ 1/10^12
    · exact leaf_short_weight_tiny_cutoff h4 h9 hω hz hB1 hε hε8 hεt
    · have hεt1 : 1/10^12 ≤ ε := le_of_lt (not_le.mp hεt)
      exact leaf_short_weight_large_cutoff h4 h9 hω hz hB1 hε hε8 hεt1

/-- LEAF 3 of 4. Step: build the normalised short coefficient. For a Buchstab weight with the
zero extension, a divisor exponent `B` and a cutoff `ε` in `(0, 1/10^8]`, there are a density
`v0` and a family `b0` such that `v0` is at least one minus the two discarded integrals, the
family obeys the divisor bound at exponent `B`, it obeys the centred character mean value of
`RightConditions`, and it is pointwise dominated by the prime indicator on every short
interval from some point on.

This is the construction step that turns the functional equation into a coefficient family:
the discarded parts of the two-prime and four-prime decompositions give the density ledger,
and the normalisation of the centred sums gives the mean value. Strictly easier than the
statement, which in addition has to choose `ω`, `B0` and `η`, and which asks for the
exceptional character average as well. Non-vacuity: `ε → 0` is excluded by `0 < ε`, and at
`v0 = 0` the family `b0 = 0` satisfies the divisor bound and the mean value. It fails
the positive density ledger. The no-nonpositive-witness certificate below uses only centered
distribution and the ledger, without assuming the exceptional moment. -/
theorem leaf_centered_character_mean_value
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
      1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
      (∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  exact leaf_centered_character_mean_value_split h4 h9 hω hz hε hε8

/-- LEAF 4 of 4. Step: average over characters and discard the exceptional set. For a family
`b0` that already carries the divisor bound at exponent `B` and the centred character mean
value at density `v0`, there is an exceptional set of characters per level `A` and per `x`,
whose cardinality is `O(q^(1/2) log x^(-2A))`, such that the squared centred sums over the
complement, averaged over the shifts `z` of the short interval, are
`O((q * sieveQ)^2 x^(11/20+eps) log x^(-A))`.

This is the third conjunct of `RightConditions` alone: it consumes the two boundedness
properties of the coefficient family and produces the exceptional set, so it does not restate
the statement and does not assert the pointwise domination. Non-vacuity: `b0 = 0` and
`v0 = 0` satisfy the two hypotheses, and then the empty exceptional set satisfies the
conclusion, so the leaf is neither vacuous nor refutable at that reading. Its content is the
case where `b0` is the normalised coefficient of leaf 3, which is why it is stated on the
boundedness properties only. -/
theorem leaf_exceptional_set_moment
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε v0 : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    {b0 : ℝ → ℕ → ℝ}
    (hbd : ∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (hchar : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((b0 x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- The sealed statement, assembled from the four leaves above with no sorry. Leaf 1 supplies
`ω` with its zero extension, leaf 2 the divisor exponent `B0` and the threshold `η` together
with the conversion `ε < η → 0 < ε ∧ ε ≤ 1/10^8`, leaf 3 the density `v0` and the coefficient
family `b0` with its density ledger, divisor bound, character mean value and prime domination,
and leaf 4 the exceptional character set that completes `RightConditions`. No step uses the
sealed theorem. -/
theorem lower_short_weight_analytic_split (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ ω : ℝ → ℝ,
      LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω ∧
      LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω ∧
      ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
        ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
          1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
          RightConditions ε B v0 b0 ∧
          ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
            ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  obtain ⟨ω, hω, hz⟩ := leaf_buchstab_model_exists
  obtain ⟨B0, η, hη, hη8, hrange⟩ := leaf_thresholds
  refine ⟨ω, hω, hz, B0, η, hη, ?_⟩
  intro B ε hB hε hεη
  obtain ⟨hε0, hε8⟩ := hrange B ε hB hε hεη
  obtain ⟨v0, b0, hv0, hbd, hchar, hsand⟩ :=
    leaf_centered_character_mean_value h4 h9 hω hz hε0 hε8
  obtain ⟨E, hE⟩ := leaf_exceptional_set_moment h4 h9 hω hz hε0 hε8 hbd hchar
  exact ⟨v0, b0, hv0, ⟨hbd, hchar, ⟨E, hE⟩⟩, hsand⟩

/-- Page 3, display 1.8. Ordered short weights have ordered densities using
only centered distribution. The divisor bound and exceptional moment are unnecessary.
The argument specializes the existing DensityMono1609 proof to its used premises. -/
theorem centered_distribution_density_mono {ε v0 v1 : ℝ} {b0 b1 : ℝ → ℕ → ℝ} (hε : 0 < ε)
    (h0 : Task308.ShortDistribution ε v0 b0)
    (h1 : Task308.ShortDistribution ε v1 b1)
    (hs : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, b0 x m ≤ b1 x m) : v0 ≤ v1 := by
  by_contra hcon
  have hδ : 0 < v0 - v1 := by linarith [not_le.mp hcon]
  obtain ⟨X, hX⟩ := hs
  obtain ⟨C0, hC0⟩ := h0 2 (by norm_num)
  obtain ⟨C1, hC1⟩ := h1 2 (by norm_num)
  set θ : ℝ := 11 / 20 + ε with hθ
  have hθ0 : 0 < θ := by positivity
  set K : ℝ := |C0| + |C1| + 1 with hK
  have hK0 : 0 < K := by positivity
  set Y : ℝ := max (max X (max C0 C1)) (max 4 (Real.exp (4 * θ * K / (v0 - v1) + 1))) with hY
  have hxX : X ≤ Y := (le_max_left _ _).trans (le_max_left _ _)
  have hxC0 : C0 ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hxC1 : C1 ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hx4 : 4 ≤ Y := (le_max_left _ _).trans (le_max_right _ _)
  have hxe : Real.exp (4 * θ * K / (v0 - v1) + 1) ≤ Y :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hY0 : 0 < Y := by linarith
  have hlogbig : 4 * θ * K / (v0 - v1) + 1 ≤ Real.log Y := by
    have := Real.log_le_log (Real.exp_pos _) hxe
    rwa [Real.log_exp] at this
  have hfrac : 0 ≤ 4 * θ * K / (v0 - v1) := by positivity
  have hlog1 : 1 ≤ Real.log Y := by linarith
  have hlogpos : 0 < Real.log Y := by linarith
  set H : ℝ := Y ^ θ with hH
  have hH2 : 2 ≤ H := by
    have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    calc (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := h4.symm
      _ ≤ Y ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hx4 (by norm_num)
      _ ≤ Y ^ θ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [hθ]; linarith)
  set Λ : ℝ := Real.log H with hΛ
  have hΛv : Λ = θ * Real.log Y := by rw [hΛ, hH, Real.log_rpow hY0]
  have hΛ0 : 0 < Λ := by rw [hΛv]; positivity
  have hχ : ∀ z : ZMod 1, (1 : DirichletCharacter ℂ 1) z = 1 := by
    intro z
    apply MulChar.one_apply
    have hz : z = 1 := Subsingleton.elim _ _
    rw [hz]
    exact isUnit_one
  have hq1 : ((1 : ℕ) : ℝ) ≤ Real.log Y ^ (2 : ℝ) := by
    simpa using Real.one_le_rpow hlog1 (by norm_num : (0 : ℝ) ≤ 2)
  have hrp : Real.log Y ^ (-2 : ℝ) = (Real.log Y ^ 2)⁻¹ := by
    rw [Real.rpow_neg hlogpos.le]
    norm_num
  have mean : ∀ (C v : ℝ) (b : ℝ → ℕ → ℝ),
      ‖∑ m ∈ (rightInterval ε Y).filter (fun m : ℕ => (m : ℝ) ≤ 2 * H),
        ((b Y m : ℂ) * (1 : DirichletCharacter ℂ 1) (m : ZMod 1) -
          Thm2.delta (1 : DirichletCharacter ℂ 1) * v / Real.log H)‖ ≤ C * H * Real.log Y ^ (-2 : ℝ) →
      |∑ m ∈ rightInterval ε Y, (b Y m - v / Λ)| ≤ C * H * (Real.log Y ^ 2)⁻¹ := by
    intro C v b h
    have hfil : (rightInterval ε Y).filter (fun m : ℕ => (m : ℝ) ≤ 2 * H) = rightInterval ε Y := by
      apply Finset.filter_true_of_mem
      intro m hm
      have hm2 := (Finset.mem_Ioc.mp hm).2
      have hnn : 0 ≤ 2 * H := by positivity
      exact (Nat.le_floor_iff hnn).mp hm2
    rw [hfil] at h
    have he : ∑ m ∈ rightInterval ε Y,
        ((b Y m : ℂ) * (1 : DirichletCharacter ℂ 1) (m : ZMod 1) -
          Thm2.delta (1 : DirichletCharacter ℂ 1) * v / Real.log H) =
        ((∑ m ∈ rightInterval ε Y, (b Y m - v / Λ) : ℝ) : ℂ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro m _
      rw [hχ]
      simp [Thm2.delta, hΛ]
    rw [he, Complex.norm_real, Real.norm_eq_abs, hrp] at h
    exact h
  have hb0 := mean C0 v0 b0 (hC0 Y hxC0 1 le_rfl hq1 1 (2 * H) le_rfl)
  have hb1 := mean C1 v1 b1 (hC1 Y hxC1 1 le_rfl hq1 1 (2 * H) le_rfl)
  set I := rightInterval ε Y with hI
  have hcard : H / 2 ≤ (I.card : ℝ) := by
    have hc : I.card = ⌊2 * H⌋₊ - ⌊H⌋₊ := by rw [hI, rightInterval, Nat.card_Ioc]
    have hle : ⌊H⌋₊ ≤ ⌊2 * H⌋₊ := Nat.floor_mono (by linarith)
    rw [hc, Nat.cast_sub hle]
    have h1 := Nat.lt_floor_add_one (2 * H)
    have h2 := Nat.floor_le (show 0 ≤ H by linarith)
    linarith
  have hdiff : (v0 - v1) * (I.card : ℝ) / Λ ≤
      (∑ m ∈ I, (b1 Y m - v1 / Λ)) - ∑ m ∈ I, (b0 Y m - v0 / Λ) := by
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ m ∈ I, (v0 - v1) / Λ ≤ (b1 Y m - v1 / Λ) - (b0 Y m - v0 / Λ) := by
      intro m hm
      have := hX Y hxX m hm
      have he : (v0 - v1) / Λ = v0 / Λ - v1 / Λ := sub_div _ _ _
      linarith
    calc (v0 - v1) * (I.card : ℝ) / Λ = ∑ _m ∈ I, (v0 - v1) / Λ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ _ := Finset.sum_le_sum hterm
  have hA := (le_abs_self _).trans hb1
  have hB := (neg_abs_le _).trans' (neg_le_neg hb0)
  have hsum : (v0 - v1) * (I.card : ℝ) / Λ ≤ (C0 + C1) * H * (Real.log Y ^ 2)⁻¹ := by
    have hexp : (C0 + C1) * H * (Real.log Y ^ 2)⁻¹ =
        C0 * H * (Real.log Y ^ 2)⁻¹ + C1 * H * (Real.log Y ^ 2)⁻¹ := by ring
    linarith
  have hCK : C0 + C1 ≤ K := by
    rw [hK]
    linarith [le_abs_self C0, le_abs_self C1]
  have hHpos : 0 < H := by linarith
  have hinvnn : 0 ≤ (Real.log Y ^ 2)⁻¹ := by positivity
  have h1 : (v0 - v1) * (H / 2) / Λ ≤ K * H * (Real.log Y ^ 2)⁻¹ :=
    calc (v0 - v1) * (H / 2) / Λ ≤ (v0 - v1) * (I.card : ℝ) / Λ := by gcongr
      _ ≤ (C0 + C1) * H * (Real.log Y ^ 2)⁻¹ := hsum
      _ ≤ K * H * (Real.log Y ^ 2)⁻¹ := by gcongr
  rw [hΛv] at h1
  have h2 : (v0 - v1) * Real.log Y ≤ 2 * θ * K := by
    have hne := hlogpos.ne'
    have hthne := hθ0.ne'
    have hHne := hHpos.ne'
    have heq : (v0 - v1) * (H / 2) / (θ * Real.log Y) * (2 * θ * Real.log Y ^ 2 / H) =
        (v0 - v1) * Real.log Y := by
      field_simp
    have heq2 : K * H * (Real.log Y ^ 2)⁻¹ * (2 * θ * Real.log Y ^ 2 / H) = 2 * θ * K := by
      field_simp
    have hmul := mul_le_mul_of_nonneg_right h1
      (show 0 ≤ 2 * θ * Real.log Y ^ 2 / H by positivity)
    rwa [heq, heq2] at hmul
  have h3 : 4 * θ * K ≤ (v0 - v1) * Real.log Y := by
    have hh : 4 * θ * K / (v0 - v1) ≤ Real.log Y := by linarith
    rw [div_le_iff₀ hδ] at hh
    linarith
  have hpos : 0 < θ * K := by positivity
  linarith


/-- Pages 3 and 51, displays 1.8 and 5.17. A nonpositive family cannot meet
the positive Buchstab ledger and centered distribution in leaf 3. No moment premise is used. -/
theorem leaf_no_nonpos_centered_witness
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ¬ ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
      1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
      Task308.ShortDistribution ε v0 b0 ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, b0 x m ≤ 0 := by
  rintro ⟨v0, b0, hv0, hchar, hnonpos⟩
  have hp := leaf_lower_density_gt hω hz hε hε8 hv0
  have hle := centered_distribution_density_mono hε hchar
    (Task308.short_distribution_zero ε) hnonpos
  linarith


/-- Page 3, display 1.8 at the principal character modulo one and t equal to 2Y.
This is the precise scalar mass estimate forced by centered distribution. -/
theorem centered_principal_mass_bound {ε v : ℝ} {b : ℝ → ℕ → ℝ}
    (hchar : Task308.ShortDistribution ε v b) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      |(∑ m ∈ rightInterval ε x, b x m) -
        ((rightInterval ε x).card : ℝ) * v / Real.log (x ^ (11 / 20 + ε))| ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C0, hC0⟩ := hchar A hA
  let C := max C0 (Real.exp 1)
  refine ⟨C, fun x hx => ?_⟩
  have hxC0 : C0 ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hxe
  have hl : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hxe
  have hq : (1 : ℝ) ≤ Real.log x ^ A := Real.one_le_rpow hl hA.le
  have hc := hC0 x hxC0 1 le_rfl (by simpa using hq) 1 (2 * x ^ (11 / 20 + ε)) le_rfl
  have hf : (rightInterval ε x).filter (fun m : ℕ =>
      (m : ℝ) ≤ 2 * x ^ (11 / 20 + ε)) = rightInterval ε x := by
    apply Finset.filter_true_of_mem
    intro m hm
    exact (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Ioc.mp hm).2
  have hχ : ∀ m : ℕ, (1 : DirichletCharacter ℂ 1) (m : ZMod 1) = 1 := by
    intro m
    rw [Subsingleton.elim (m : ZMod 1) 1, map_one]
  rw [hf] at hc
  simp_rw [hχ] at hc
  have he : (∑ m ∈ rightInterval ε x,
      ((b x m : ℂ) * 1 - Thm2.delta (1 : DirichletCharacter ℂ 1) * v /
        Real.log (x ^ (11 / 20 + ε)))) =
      (((∑ m ∈ rightInterval ε x, b x m) -
        ((rightInterval ε x).card : ℝ) * v / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ) := by
    simp [Thm2.delta, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      mul_div_assoc]
  rw [he, Complex.norm_real, Real.norm_eq_abs] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _))
      (Real.rpow_nonneg (by linarith) _))

/-- Pages 3 and 51, displays 1.8 and 5.17. Prime domination and centered
positive density force a quantitative lower bound on the prime count in J. -/
theorem centered_prime_count_lower {ε v : ℝ} {b : ℝ → ℕ → ℝ}
    (hchar : Task308.ShortDistribution ε v b)
    (hsand : ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ m ∈ rightInterval ε x, b x m ≤ primeWeight m) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      ((rightInterval ε x).card : ℝ) * v / Real.log (x ^ (11 / 20 + ε)) -
        C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) ≤
          (((rightInterval ε x).filter Nat.Prime).card : ℝ) := by
  intro A hA
  obtain ⟨C0, hC0⟩ := centered_principal_mass_bound hchar A hA
  obtain ⟨X, hX⟩ := hsand
  let C := max C0 (max X 1)
  refine ⟨C, fun x hx => ?_⟩
  have hxC0 : C0 ≤ x := (le_max_left _ _).trans hx
  have hxX : X ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx1 : 1 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hc := hC0 x hxC0
  have hsum := Finset.sum_le_sum (hX x hxX)
  have he : (∑ m ∈ rightInterval ε x, primeWeight m) =
      (((rightInterval ε x).filter Nat.Prime).card : ℝ) := by
    simp [primeWeight, Finset.sum_boole]
  rw [he] at hsum
  have hscale : C0 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) ≤
      C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _))
      (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  linarith [neg_abs_le ((∑ m ∈ rightInterval ε x, b x m) -
    ((rightInterval ε x).card : ℝ) * v / Real.log (x ^ (11 / 20 + ε)))]


/-- Page 3, display 1.9. A closed local window is the difference of the
weak upper prefix and strict lower prefix. The strict endpoint is essential. -/
theorem centered_window_eq_prefix_sub (S : Finset ℕ) (f : ℕ → ℂ)
    {l u : ℝ} (hlu : l ≤ u) :
    (∑ m ∈ S.filter (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ u), f m) =
      (∑ m ∈ S.filter (fun m : ℕ => (m : ℝ) ≤ u), f m) -
        ∑ m ∈ S.filter (fun m : ℕ => (m : ℝ) < l), f m := by
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hl : (m : ℝ) < l
  · have hu : (m : ℝ) ≤ u := hl.le.trans hlu
    simp [hl, hu, not_le.mpr hl]
  · have hl' : l ≤ (m : ℝ) := le_of_not_gt hl
    simp [hl, hl']

/-- Page 3, displays 1.8 and 1.9. Two uniform prefix bounds give a local
window bound of twice the same error. This step gives no short-window saving. -/
theorem centered_window_norm_le (S : Finset ℕ) (f : ℕ → ℂ)
    {l u D : ℝ} (hlu : l ≤ u)
    (hu : ‖∑ m ∈ S.filter (fun m : ℕ => (m : ℝ) ≤ u), f m‖ ≤ D)
    (hl : ‖∑ m ∈ S.filter (fun m : ℕ => (m : ℝ) < l), f m‖ ≤ D) :
    ‖∑ m ∈ S.filter (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ u), f m‖ ≤ 2 * D := by
  rw [centered_window_eq_prefix_sub S f hlu]
  exact (norm_sub_le _ _).trans (by linarith)

/-- Page 3, display 1.9. Integrating a uniform prefix-derived error 2D
on the stated y interval gives 10 times D squared times Y. -/
theorem centered_window_moment_of_uniform_bound {Y D : ℝ} (hY : 0 ≤ Y) (hD : 0 ≤ D)
    (F : ℝ → ℂ)
    (hi : IntervalIntegrable (fun y => ‖F y‖ ^ 2) MeasureTheory.volume (Y / 2) (3 * Y))
    (hb : ∀ y ∈ Set.Icc (Y / 2) (3 * Y), ‖F y‖ ≤ 2 * D) :
    (∫ y in (Y / 2)..(3 * Y), ‖F y‖ ^ 2) ≤ 10 * D ^ 2 * Y := by
  have hh := intervalIntegral.integral_mono_on (show Y / 2 ≤ 3 * Y by linarith)
    hi (intervalIntegrable_const (c := (2 * D) ^ 2))
    (fun y hy => pow_le_pow_left₀ (norm_nonneg _) (hb y hy) 2)
  calc
    _ ≤ ∫ _y in (Y / 2)..(3 * Y), (2 * D) ^ 2 := hh
    _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring


/-- Page 3, display 1.9. At modulus one the exceptional set is eventually
empty for every positive logarithmic exponent. Thus the principal local
moment itself must have the prescribed logarithmic saving. -/
theorem short_moment_principal_log_saving {ε v : ℝ} {b : ℝ → ℕ → ℝ}
    (hm : Task308.ShortMeanSquare ε v b) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → 1 ≤ sieveQ ε x →
      (∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ =>
          y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * ((sieveQ ε x : ℝ) / x ^ (11 / 20 + ε))),
          ((b x m : ℂ) * (1 : DirichletCharacter ℂ 1) (m : ZMod 1) -
            Thm2.delta (1 : DirichletCharacter ℂ 1) * v /
              Real.log (x ^ (11 / 20 + ε)))‖ ^ 2) ≤
        C * (sieveQ ε x : ℝ) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨E, hE⟩ := hm
  obtain ⟨C0, hC0⟩ := hE A hA
  have hdec : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ (-2 * A) < 1 / (|C0| + 1) := by
    have ht := (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 2 * A)).comp
      Real.tendsto_log_atTop
    simpa only [Function.comp_apply, neg_mul] using ht.eventually
      (eventually_lt_nhds (show (0 : ℝ) < 1 / (|C0| + 1) by positivity))
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hdec
  let C := max 1 (max C0 X)
  refine ⟨C, fun x hx hQ => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hxC : C0 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxX : X ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  obtain ⟨hc, he⟩ := hC0 x hxC 1 le_rfl hQ
  simp only [Nat.cast_one, Real.one_rpow, mul_one] at hc
  have hsmall : C0 * Real.log x ^ (-2 * A) < 1 := by
    calc
      _ ≤ (|C0| + 1) * Real.log x ^ (-2 * A) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self C0])
          (Real.rpow_nonneg (Real.log_nonneg hx1) _)
      _ < (|C0| + 1) * (1 / (|C0| + 1)) :=
        mul_lt_mul_of_pos_left (hX x hxX) (by positivity)
      _ = 1 := by field_simp
  have hcard : (E A x 1).card < 1 := by exact_mod_cast hc.trans_lt hsmall
  have hempty : E A x 1 = ∅ := Finset.card_eq_zero.mp (by omega)
  have huni : (Finset.univ : Finset (DirichletCharacter ℂ 1)) = {1} := by
    ext χ
    constructor
    · intro _
      apply Finset.mem_singleton.mpr
      apply DFunLike.ext
      intro z
      rw [Subsingleton.elim z (1 : ZMod 1), map_one, map_one]
    · intro _
      exact Finset.mem_univ χ
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
  have hQ0 : (0 : ℝ) ≤ sieveQ ε x := Nat.cast_nonneg _
  have hl : ((1 : ℕ) * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤
      (sieveQ ε x : ℝ) / x ^ (11 / 20 + ε) := by
    simp only [Nat.cast_one, one_mul]
    apply (div_le_div_iff₀ (by positivity) hY).mpr
    nlinarith
  have hu : (sieveQ ε x : ℝ) / x ^ (11 / 20 + ε) ≤
      6 * 1 * sieveQ ε x / x ^ (11 / 20 + ε) := by
    apply div_le_div_of_nonneg_right _ hY.le
    nlinarith
  have hh := he ((sieveQ ε x : ℝ) / x ^ (11 / 20 + ε)) (by simpa using hl) (by simpa using hu)
  simp only [hempty, Finset.sdiff_empty, huni, Finset.sum_singleton, Nat.cast_one,
    one_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ((le_max_left C0 X).trans (le_max_right 1 _))
        (sq_nonneg _)) (Real.rpow_nonneg hx0.le _))
      (Real.rpow_nonneg (Real.log_nonneg hx1) _))


/-- Page 3, displays 1.8 and 1.9. Centered distribution bounds every interior
closed window by twice the global prefix error. A ceiling supplies the strict
lower prefix without losing a single coefficient at an integer endpoint. -/
theorem centered_window_norm_of_distribution {ε v : ℝ} {b : ℝ → ℕ → ℝ}
    (hd : Task308.ShortDistribution ε v b) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
      ∀ l u : ℝ, 0 < l → l ≤ u → u ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ u),
          ((b x m : ℂ) * χ (m : ZMod q) -
            Thm2.delta χ * v / Real.log (x ^ (11 / 20 + ε)))‖ ≤
          2 * C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C, hC⟩ := hd A hA
  refine ⟨C, fun x hx q hq hqx χ l u hl hlu hu => ?_⟩
  have hcut : (⌈l⌉₊ : ℝ) - 1 ≤ 2 * x ^ (11 / 20 + ε) := by
    have hc := Nat.ceil_lt_add_one hl.le
    linarith
  have hf : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) < l) =
      (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ (⌈l⌉₊ : ℝ) - 1) := by
    apply Finset.filter_congr
    intro m hm
    constructor
    · intro hml
      have hn : m + 1 ≤ ⌈l⌉₊ := Nat.lt_ceil.mpr hml
      have hr : (m : ℝ) + 1 ≤ (⌈l⌉₊ : ℝ) := by exact_mod_cast hn
      linarith
    · intro hml
      have hr : (m : ℝ) + 1 ≤ (⌈l⌉₊ : ℝ) := by linarith
      have hn : m + 1 ≤ ⌈l⌉₊ := by exact_mod_cast hr
      exact Nat.lt_ceil.mp (by omega)
  have hlo := hC x hx q hq hqx χ ((⌈l⌉₊ : ℝ) - 1) hcut
  rw [← hf] at hlo
  have hh := centered_window_norm_le (rightInterval ε x)
    (fun m => (b x m : ℂ) * χ (m : ZMod q) -
      Thm2.delta χ * v / Real.log (x ^ (11 / 20 + ε))) hlu
      (hC x hx q hq hqx χ u hu) hlo
  calc
    _ ≤ 2 * (C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := hh
    _ = _ := by ring


/-! Page 3, auxiliary investigation of the universal-family moment leaf.
The balanced block family has a divisor bound at exponent zero and centered
distribution at density zero. These are elementary diagnostics, not a claim
that the paper defines this family. The local moment lower bound and counterexample are given below. The full
negated leaf type retains its two original cited inputs as hypotheses. AI wrote the Lean code. Goldbach is open.
-/
namespace BlockDiagnostic479
open Classical Complex Finset

theorem periodic_full_sum (g : ℕ → ℂ) (q : ℕ) (hg : Function.Periodic g q) (a : ℕ) :
    (∑ i ∈ Finset.range q, g (a + i)) = ∑ i ∈ Finset.range q, g i := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h0 := Finset.sum_range_succ (fun i => g (a + i)) q
    have h1 := Finset.sum_range_succ' (fun i => g (a + i)) q
    have hp : g (a + q) = g a := hg a
    have he : (∑ i ∈ Finset.range q, g (a + (i + 1))) =
        ∑ i ∈ Finset.range q, g (a + 1 + i) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      omega
    rw [he] at h1
    rw [hp, ih] at h0
    have hh : (∑ i ∈ Finset.range q, g i) + g a =
        (∑ i ∈ Finset.range q, g (a + 1 + i)) + g a := h0.symm.trans h1
    exact add_right_cancel hh.symm


theorem periodic_blocks_sum (g : ℕ → ℂ) (q : ℕ) (hg : Function.Periodic g q)
    (a k : ℕ) : (∑ i ∈ Finset.range (q * k), g (a + i)) =
      k • (∑ i ∈ Finset.range q, g i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have hs : (∑ i ∈ Finset.range q, g (a + (q * k + i))) =
        ∑ i ∈ Finset.range q, g (a + q * k + i) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      omega
    rw [hs, periodic_full_sum g q hg (a + q * k), add_nsmul]
    simp

theorem periodic_prefix_remainder (g : ℕ → ℂ) (q : ℕ) (hg : Function.Periodic g q)
    (a N : ℕ) : (∑ i ∈ Finset.range N, g (a + i)) =
      (N / q) • (∑ i ∈ Finset.range q, g i) +
        ∑ i ∈ Finset.range (N % q), g (a + q * (N / q) + i) := by
  calc
    _ = ∑ i ∈ Finset.range (q * (N / q) + N % q), g (a + i) := by rw [Nat.div_add_mod]
    _ = _ := by
      rw [Finset.sum_range_add, periodic_blocks_sum g q hg]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      omega

theorem periodic_prefix_error (g : ℕ → ℂ) (q : ℕ) (hq : 0 < q)
    (hg : Function.Periodic g q) (hb : ∀ n, ‖g n‖ ≤ 1) (a N : ℕ) :
    ‖(∑ i ∈ Finset.range N, g (a + i)) -
      (N / q) • (∑ i ∈ Finset.range q, g i)‖ ≤ q := by
  rw [periodic_prefix_remainder g q hg a N, add_sub_cancel_left]
  calc
    _ ≤ ∑ i ∈ Finset.range (N % q), ‖g (a + q * (N / q) + i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (N % q), (1 : ℝ) := Finset.sum_le_sum (fun i hi => hb _)
    _ = (N % q : ℕ) := by simp
    _ ≤ (q : ℝ) := by exact_mod_cast (Nat.mod_lt N hq).le

theorem periodic_equal_length_difference (g : ℕ → ℂ) (q : ℕ) (hq : 0 < q)
    (hg : Function.Periodic g q) (hb : ∀ n, ‖g n‖ ≤ 1) (a b L : ℕ) :
    ‖(∑ i ∈ Finset.range L, g (a + i)) -
      (∑ i ∈ Finset.range L, g (b + i))‖ ≤ 2 * q := by
  have ha := periodic_prefix_error g q hq hg hb a L
  have hb' := periodic_prefix_error g q hq hg hb b L
  have he : (∑ i ∈ Finset.range L, g (a + i)) -
      (∑ i ∈ Finset.range L, g (b + i)) =
      ((∑ i ∈ Finset.range L, g (a + i)) - (L / q) • (∑ i ∈ Finset.range q, g i)) -
      ((∑ i ∈ Finset.range L, g (b + i)) - (L / q) • (∑ i ∈ Finset.range q, g i)) := by ring
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)


noncomputable def blockSign (L n : ℕ) : ℝ := (-1 : ℝ) ^ (n / L)

theorem blockSign_abs (L n : ℕ) : |blockSign L n| = 1 := by
  simp [blockSign, abs_pow]

theorem block_pair_sum (g : ℕ → ℂ) {L : ℕ} (hL : 0 < L) (j : ℕ) :
    (∑ i ∈ Finset.range (2 * L), (blockSign L (2 * L * j + i) : ℂ) * g (2 * L * j + i)) =
      (∑ i ∈ Finset.range L, g (2 * L * j + i)) -
        ∑ i ∈ Finset.range L, g (2 * L * j + L + i) := by
  have h0 (i : ℕ) (hi : i < L) : blockSign L (2 * L * j + i) = 1 := by
    have he : 2 * L * j + i = i + L * (2 * j) := by ring
    simp only [blockSign, he, Nat.add_mul_div_left i (2 * j) hL,
      Nat.div_eq_of_lt hi, zero_add, pow_mul]
    norm_num
  have h1 (i : ℕ) (hi : i < L) : blockSign L (2 * L * j + L + i) = -1 := by
    have he : 2 * L * j + L + i = i + L * (2 * j + 1) := by ring
    simp only [blockSign, he, Nat.add_mul_div_left i (2 * j + 1) hL,
      Nat.div_eq_of_lt hi, zero_add, pow_add, pow_mul]
    norm_num
  have he : (2 * L : ℕ) = L + L := by omega
  have hs := Finset.sum_range_add
    (fun i => (blockSign L (2 * L * j + i) : ℂ) * g (2 * L * j + i)) L L
  rw [← he] at hs
  rw [hs]
  have hleft : (∑ i ∈ Finset.range L, (blockSign L (2 * L * j + i) : ℂ) * g (2 * L * j + i)) =
      ∑ i ∈ Finset.range L, g (2 * L * j + i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [h0 i (Finset.mem_range.mp hi)]
    simp
  have hright : (∑ i ∈ Finset.range L, (blockSign L (2 * L * j + (L + i)) : ℂ) *
      g (2 * L * j + (L + i))) = -(∑ i ∈ Finset.range L, g (2 * L * j + L + i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show 2 * L * j + (L + i) = 2 * L * j + L + i by omega,
      h1 i (Finset.mem_range.mp hi)]
    simp
  rw [hleft, hright]
  exact sub_eq_add_neg _ _ |>.symm

theorem block_pair_norm (g : ℕ → ℂ) (q : ℕ) (hq : 0 < q)
    (hg : Function.Periodic g q) (hb : ∀ n, ‖g n‖ ≤ 1)
    {L : ℕ} (hL : 0 < L) (j : ℕ) :
    ‖∑ i ∈ Finset.range (2 * L), (blockSign L (2 * L * j + i) : ℂ) * g (2 * L * j + i)‖ ≤
      2 * q := by
  rw [block_pair_sum g hL j]
  exact periodic_equal_length_difference g q hq hg hb _ _ _


theorem block_full_pairs_norm (g : ℕ → ℂ) (q : ℕ) (hq : 0 < q)
    (hg : Function.Periodic g q) (hb : ∀ n, ‖g n‖ ≤ 1)
    {L : ℕ} (hL : 0 < L) (k : ℕ) :
    ‖∑ i ∈ Finset.range (2 * L * k), (blockSign L i : ℂ) * g i‖ ≤ (k : ℝ) * (2 * q) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add]
    calc
      _ ≤ ‖∑ i ∈ Finset.range (2 * L * k), (blockSign L i : ℂ) * g i‖ +
          ‖∑ i ∈ Finset.range (2 * L), (blockSign L (2 * L * k + i) : ℂ) * g (2 * L * k + i)‖ :=
        norm_add_le _ _
      _ ≤ (k : ℝ) * (2 * q) + 2 * q := add_le_add ih (block_pair_norm g q hq hg hb hL k)
      _ = _ := by push_cast; ring

theorem block_prefix_norm (g : ℕ → ℂ) (q : ℕ) (hq : 0 < q)
    (hg : Function.Periodic g q) (hb : ∀ n, ‖g n‖ ≤ 1)
    {L : ℕ} (hL : 0 < L) (N : ℕ) :
    ‖∑ i ∈ Finset.range N, (blockSign L i : ℂ) * g i‖ ≤
      (N / (2 * L) : ℕ) * (2 * (q : ℝ)) + 2 * L := by
  have he := Nat.div_add_mod N (2 * L)
  have hs := Finset.sum_range_add (fun i => (blockSign L i : ℂ) * g i)
    (2 * L * (N / (2 * L))) (N % (2 * L))
  rw [he] at hs
  rw [hs]
  have hr : ‖∑ i ∈ Finset.range (N % (2 * L)),
      (blockSign L (2 * L * (N / (2 * L)) + i) : ℂ) * g (2 * L * (N / (2 * L)) + i)‖ ≤
        (2 * L : ℕ) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (N % (2 * L)),
          ‖(blockSign L (2 * L * (N / (2 * L)) + i) : ℂ) * g (2 * L * (N / (2 * L)) + i)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range (N % (2 * L)), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, blockSign_abs, one_mul]
        exact hb _
      _ = (N % (2 * L) : ℕ) := by simp
      _ ≤ (2 * L : ℕ) := by exact_mod_cast (Nat.mod_lt N (by omega : 0 < 2 * L)).le
  exact (norm_add_le _ _).trans (by
    have hh := block_full_pairs_norm g q hq hg hb hL (N / (2 * L))
    push_cast at hr
    exact add_le_add hh hr)


theorem block_prefix_sqrt_bound (g : ℕ → ℂ) (q : ℕ) (hq : 0 < q)
    (hg : Function.Periodic g q) (hb : ∀ n, ‖g n‖ ≤ 1)
    {L : ℕ} (hL : 0 < L) {R : ℝ} (hR : 2 ≤ R)
    (hLle : (L : ℝ) ≤ R) (hRle : R ≤ 2 * (L : ℝ))
    (N : ℕ) (hN : (N : ℝ) ≤ 3 * R ^ 2) :
    ‖∑ i ∈ Finset.range N, (blockSign L i : ℂ) * g i‖ ≤
      (6 * (q : ℝ) + 2) * R := by
  let D : ℝ := (N / (2 * L) : ℕ)
  have hD0 : 0 ≤ D := Nat.cast_nonneg _
  have hDR : D * (2 * L) ≤ (N : ℝ) := by
    dsimp [D]
    have hh := Nat.mul_div_le N (2 * L)
    have hh' : (2 * L : ℝ) * (N / (2 * L) : ℕ) ≤ N := by exact_mod_cast hh
    nlinarith
  have hD : D ≤ 3 * R := by
    apply (mul_le_mul_iff_right₀ (show 0 < R by linarith)).mp
    have hh := mul_le_mul_of_nonneg_left hRle hD0
    nlinarith
  calc
    _ ≤ D * (2 * (q : ℝ)) + 2 * L := block_prefix_norm g q hq hg hb hL N
    _ ≤ (3 * R) * (2 * (q : ℝ)) + 2 * R :=
      add_le_add (mul_le_mul_of_nonneg_right hD (by positivity)) (by linarith)
    _ = _ := by ring


theorem block_Ioc_sqrt_bound (g : ℕ → ℂ) (q : ℕ) (hq : 0 < q)
    (hg : Function.Periodic g q) (hb : ∀ n, ‖g n‖ ≤ 1)
    {L : ℕ} (hL : 0 < L) {R : ℝ} (hR : 2 ≤ R)
    (hLle : (L : ℝ) ≤ R) (hRle : R ≤ 2 * (L : ℝ))
    (a b : ℕ) (hab : a ≤ b) (hN : (b : ℝ) + 1 ≤ 3 * R ^ 2) :
    ‖∑ i ∈ Finset.Ioc a b, (blockSign L i : ℂ) * g i‖ ≤
      16 * (q : ℝ) * R := by
  have hs : Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) := by
    ext i
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have ha : ((a + 1 : ℕ) : ℝ) ≤ 3 * R ^ 2 := by
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    push_cast
    linarith
  have hb' : ((b + 1 : ℕ) : ℝ) ≤ 3 * R ^ 2 := by simpa using hN
  rw [hs, Finset.sum_Ico_eq_sub _ (by omega)]
  calc
    _ ≤ ‖∑ i ∈ Finset.range (b + 1), (blockSign L i : ℂ) * g i‖ +
        ‖∑ i ∈ Finset.range (a + 1), (blockSign L i : ℂ) * g i‖ := norm_sub_le _ _
    _ ≤ (6 * (q : ℝ) + 2) * R + (6 * (q : ℝ) + 2) * R :=
      add_le_add (block_prefix_sqrt_bound g q hq hg hb hL hR hLle hRle _ hb')
        (block_prefix_sqrt_bound g q hq hg hb hL hR hLle hRle _ ha)
    _ ≤ _ := by
      have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have hh := mul_le_mul_of_nonneg_right hq' (show 0 ≤ R by linarith)
      nlinarith

noncomputable def blockFamily (ε x : ℝ) (n : ℕ) : ℝ :=
  blockSign ⌊x ^ ((11 / 20 + ε) / 2)⌋₊ n

theorem blockFamily_divisor_bound (ε : ℝ) :
    ∃ C : ℝ, ∀ x k, |blockFamily ε x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ (0 : ℝ) := by
  refine ⟨1, fun x k => ?_⟩
  simp [blockFamily, blockSign_abs]


theorem blockFamily_distribution {ε : ℝ} (hθ : 0 < 11 / 20 + ε) :
    Task308.ShortDistribution ε 0 (blockFamily ε) := by
  intro A hA
  let s : ℝ := (11 / 20 + ε) / 2
  have hs : 0 < s := by dsimp [s]; linarith
  have hlarge : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ x ^ s :=
    (tendsto_rpow_atTop hs).eventually (Filter.eventually_ge_atTop 2)
  obtain ⟨Xr, hXr⟩ := Filter.eventually_atTop.mp hlarge
  have hsmall := (isLittleO_log_rpow_rpow_atTop (2 * A) hs).def
    (by norm_num : (0 : ℝ) < 1 / 16)
  obtain ⟨Xs, hXs⟩ := Filter.eventually_atTop.mp hsmall
  let C := max (Real.exp 1) (max Xr Xs)
  refine ⟨C, fun x hx q hq hqx χ t ht => ?_⟩
  have hxexp : Real.exp 1 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hxexp
  have hlog1 : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hxexp
  have hlog : 0 < Real.log x := by linarith
  have hC1 : 1 ≤ C := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).le.trans
    (le_max_left _ _)
  have hxr : Xr ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxs : Xs ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  let R : ℝ := x ^ s
  let Y : ℝ := x ^ (11 / 20 + ε)
  let L : ℕ := ⌊R⌋₊
  have hR2 : 2 ≤ R := hXr x hxr
  have hR0 : 0 < R := by linarith
  have hY : Y = R ^ 2 := by
    dsimp [Y, R]
    rw [← Real.rpow_mul_natCast hx0.le]
    congr 1
    dsimp [s]
    ring
  have hY1 : 1 ≤ Y := by rw [hY]; nlinarith
  have hY0 : 0 < Y := by linarith
  have hL : 0 < L := by
    have hh : 2 ≤ L := Nat.le_floor (by simpa using hR2)
    omega
  have hLle : (L : ℝ) ≤ R := Nat.floor_le hR0.le
  have hRle : R ≤ 2 * (L : ℝ) := by
    have hh := Nat.lt_floor_add_one R
    change R < (L : ℝ) + 1 at hh
    linarith
  have hP : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlog _
  have hsaving : 16 * (Real.log x ^ A) ^ 2 ≤ R := by
    have hh := hXs x hxs
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hh
    have he : (Real.log x ^ A) ^ 2 = Real.log x ^ (2 * A) := by
      rw [← Real.rpow_mul_natCast hlog.le]
      congr 1
      ring
    rw [← he] at hh
    change (Real.log x ^ A) ^ 2 ≤ (1 / 16 : ℝ) * R at hh
    linarith
  have hscale : 16 * Real.log x ^ A * R ≤ Y * Real.log x ^ (-A) := by
    rw [Real.rpow_neg hlog.le, ← div_eq_mul_inv, le_div_iff₀ hP, hY]
    have hh := mul_le_mul_of_nonneg_right hsaving hR0.le
    nlinarith
  have hq0 : 0 < q := by omega
  have hper : Function.Periodic (fun n : ℕ => χ (n : ZMod q)) q := by
    intro n
    change χ ((n + q : ℕ) : ZMod q) = χ (n : ZMod q)
    simp only [Nat.cast_add, ZMod.natCast_self, add_zero]
  have hbound : ∀ n : ℕ, ‖χ (n : ZMod q)‖ ≤ 1 := fun n => χ.norm_le_one _
  change ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
    ((blockSign L m : ℂ) * χ (m : ZMod q) -
      Thm2.delta χ * (0 : ℂ) / Real.log Y)‖ ≤ C * Y * Real.log x ^ (-A)
  simp only [mul_zero, zero_div, sub_zero]
  by_cases htY : t ≤ Y
  · have hempty : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro m hmI hmt
      have hmY : Y < (m : ℝ) := Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hmI).1
      linarith
    rw [hempty, Finset.sum_empty, norm_zero]
    positivity
  · have ht0 : 0 ≤ t := by linarith [not_le.mp htY]
    rw [Task387.right_prefix_eq_Ioc ht0 ht]
    have hab : ⌊Y⌋₊ ≤ ⌊t⌋₊ := Nat.floor_mono (not_le.mp htY).le
    have hN : (⌊t⌋₊ : ℝ) + 1 ≤ 3 * R ^ 2 := by
      have hf := Nat.floor_le ht0
      change t ≤ 2 * Y at ht
      rw [← hY]
      linarith
    have hh := block_Ioc_sqrt_bound (fun n : ℕ => χ (n : ZMod q)) q hq0 hper hbound
      hL hR2 hLle hRle ⌊Y⌋₊ ⌊t⌋₊ hab hN
    calc
      _ ≤ 16 * (q : ℝ) * R := hh
      _ ≤ 16 * Real.log x ^ A * R := by gcongr
      _ ≤ Y * Real.log x ^ (-A) := hscale
      _ ≤ _ := by
        have hb := mul_le_mul_of_nonneg_right hC1
          (show 0 ≤ Y * Real.log x ^ (-A) by positivity)
        nlinarith

theorem block_window_norm (S : Finset ℕ) {L j : ℕ} (hL : 0 < L) {y z : ℝ}
    (hlo : (j : ℝ) * L ≤ y) (hup : y + y * z < ((j + 1 : ℕ) : ℝ) * L) :
    ‖Task387.windowSum S (fun m => (blockSign L m : ℂ)) z y‖ =
      ((Task387.window S y z).card : ℝ) := by
  have hc : ∀ m ∈ Task387.window S y z, blockSign L m = (-1 : ℝ) ^ j := by
    intro m hm
    have hm' := Finset.mem_filter.mp hm
    have hnlo : j * L ≤ m := by exact_mod_cast hlo.trans hm'.2.1
    have hnhi : m < (j + 1) * L := by exact_mod_cast hm'.2.2.trans_lt hup
    simp only [blockSign, Nat.div_eq_of_lt_le hnlo hnhi]
  have he : Task387.windowSum S (fun m => (blockSign L m : ℂ)) z y =
      ∑ _m ∈ Task387.window S y z, (((-1 : ℝ) ^ j : ℝ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro m hm
    exact congrArg (fun r : ℝ => (r : ℂ)) (hc m hm)
  rw [he, Finset.sum_const, nsmul_eq_mul, norm_mul]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_pow]

theorem block_window_norm_lower (S : Finset ℕ) {L j : ℕ} (hL : 0 < L) {y z : ℝ}
    (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hs : Finset.Icc ⌈y⌉₊ ⌊y + y * z⌋₊ ⊆ S)
    (hlo : (j : ℝ) * L ≤ y) (hup : y + y * z < ((j + 1 : ℕ) : ℝ) * L) :
    y * z - 1 ≤ ‖Task387.windowSum S (fun m => (blockSign L m : ℂ)) z y‖ := by
  rw [block_window_norm S hL hlo hup]
  have hc := Task387.window_card_length_error hy hz hs
  linarith [(abs_le.mp hc).1]


theorem safe_block_window_lower {Y Q : ℝ} {L j : ℕ}
    (hY : 0 < Y) (hL : 0 < L) (hQ : 2 ≤ Q)
    (hQL : 8 * Q ≤ (L : ℝ)) (hLY : 16 * (L : ℝ) ≤ Y)
    (hjlo : Y ≤ (j : ℝ) * L)
    (hjhi : (j : ℝ) * L + (L : ℝ) / 2 ≤ 3 * Y / 2)
    {y : ℝ} (hy : y ∈ Set.Icc ((j : ℝ) * L + 1) ((j : ℝ) * L + (L : ℝ) / 2)) :
    Q / 2 ≤ ‖Task387.windowSum (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊)
      (fun m => (blockSign L m : ℂ)) (Q / Y) y‖ := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hyY : Y < y := by linarith [hy.1]
  have hy0 : 0 ≤ y := by linarith
  have hz0 : 0 ≤ Q / Y := by positivity
  have hyhi : y ≤ 3 * Y / 2 := hy.2.trans hjhi
  have hlenlo : Q ≤ y * (Q / Y) := by
    rw [← mul_div_assoc, le_div_iff₀ hY]
    nlinarith [mul_le_mul_of_nonneg_right hyY.le (show 0 ≤ Q by linarith)]
  have hlenhi : y * (Q / Y) ≤ 2 * Q := by
    rw [← mul_div_assoc, div_le_iff₀ hY]
    nlinarith [mul_le_mul_of_nonneg_right hyhi (show 0 ≤ Q by linarith)]
  have hu0 : 0 ≤ y + y * (Q / Y) := by positivity
  have huY : y + y * (Q / Y) ≤ 2 * Y := by linarith
  have hblock : y + y * (Q / Y) < ((j + 1 : ℕ) : ℝ) * L := by
    push_cast
    nlinarith [hy.2]
  have hsupport : Finset.Icc ⌈y⌉₊ ⌊y + y * (Q / Y)⌋₊ ⊆
      Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊ := by
    intro m hm
    obtain ⟨hmlo, hmhi⟩ := Finset.mem_Icc.mp hm
    have hym : y ≤ (m : ℝ) := Nat.ceil_le.mp hmlo
    have hmu : (m : ℝ) ≤ y + y * (Q / Y) := (Nat.le_floor_iff hu0).mp hmhi
    refine Finset.mem_Ioc.mpr ⟨?_, ?_⟩
    · exact (Nat.floor_lt hY.le).mpr (hyY.trans_le hym)
    · exact (Nat.le_floor_iff (by positivity : 0 ≤ 2 * Y)).mpr (hmu.trans huY)
  have hh := block_window_norm_lower (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊) hL hy0 hz0
    hsupport (show (j : ℝ) * L ≤ y by linarith [hy.1]) hblock
  linarith


theorem safe_block_positions {Y : ℝ} {L : ℕ} (hY : 0 < Y) (hL : 0 < L)
    (hLY : 16 * (L : ℝ) ≤ Y) (i : ℕ) (hi : i < ⌊Y / (4 * (L : ℝ))⌋₊) :
    Y ≤ ((⌈Y / (L : ℝ)⌉₊ + i : ℕ) : ℝ) * L ∧
    ((⌈Y / (L : ℝ)⌉₊ + i : ℕ) : ℝ) * L + (L : ℝ) / 2 ≤ 3 * Y / 2 := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have ha : Y ≤ (⌈Y / (L : ℝ)⌉₊ : ℝ) * L :=
    (div_le_iff₀ hL0).mp (Nat.le_ceil _)
  have hb : (⌈Y / (L : ℝ)⌉₊ : ℝ) * L < Y + L := by
    have hh := mul_lt_mul_of_pos_right
      (Nat.ceil_lt_add_one (show 0 ≤ Y / (L : ℝ) by positivity)) hL0
    have he : (Y / (L : ℝ) + 1) * L = Y + L := by field_simp
    rwa [he] at hh
  have hk := Nat.floor_le (show 0 ≤ Y / (4 * (L : ℝ)) by positivity)
  have hki : (i : ℝ) ≤ (⌊Y / (4 * (L : ℝ))⌋₊ : ℝ) := by exact_mod_cast hi.le
  have hiL : (i : ℝ) * L ≤ Y / 4 := by
    have hh := (le_div_iff₀ (show 0 < 4 * (L : ℝ) by positivity)).mp (hki.trans hk)
    linarith
  have hi0 : 0 ≤ (i : ℝ) * L := by positivity
  push_cast
  constructor <;> nlinarith

theorem safe_block_mass_lower {Y : ℝ} {L : ℕ} (hY : 0 < Y) (hL : 4 ≤ L)
    (hLY : 16 * (L : ℝ) ≤ Y) :
    Y / 32 ≤ (⌊Y / (4 * (L : ℝ))⌋₊ : ℝ) * ((L : ℝ) / 2 - 1) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL4 : (4 : ℝ) ≤ L := by exact_mod_cast hL
  have hk0 : 0 ≤ (⌊Y / (4 * (L : ℝ))⌋₊ : ℝ) := Nat.cast_nonneg _
  have hh := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (Y / (4 * (L : ℝ))))
    (show 0 < 4 * (L : ℝ) by positivity)
  have he : Y / (4 * (L : ℝ)) * (4 * L) = Y := by field_simp
  rw [he] at hh
  have hkL : Y / 8 ≤ (⌊Y / (4 * (L : ℝ))⌋₊ : ℝ) * L := by nlinarith
  have hw : (L : ℝ) / 4 ≤ (L : ℝ) / 2 - 1 := by linarith
  have hm := mul_le_mul_of_nonneg_left hw hk0
  nlinarith


theorem safe_block_intervals_disjoint (a : ℕ) {L : ℕ} (hL : 0 < L) :
    Pairwise (fun i j : ℕ => Disjoint
      (Set.Ioc ((((a + i : ℕ) : ℝ) * L) + 1) ((((a + i : ℕ) : ℝ) * L) + (L : ℝ) / 2))
      (Set.Ioc ((((a + j : ℕ) : ℝ) * L) + 1) ((((a + j : ℕ) : ℝ) * L) + (L : ℝ) / 2))) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have key (i j : ℕ) (hij : i < j) : Disjoint
      (Set.Ioc ((((a + i : ℕ) : ℝ) * L) + 1) ((((a + i : ℕ) : ℝ) * L) + (L : ℝ) / 2))
      (Set.Ioc ((((a + j : ℕ) : ℝ) * L) + 1) ((((a + j : ℕ) : ℝ) * L) + (L : ℝ) / 2)) := by
    have hh : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    have hmul := mul_le_mul_of_nonneg_right hh hL0.le
    apply Set.disjoint_left.mpr
    intro y hyi hyj
    have h1 := hyi.2
    have h2 := hyj.1
    push_cast at h1 h2
    nlinarith
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

theorem disjoint_interval_integrals_le (t : Finset ℕ) (a b : ℕ → ℝ)
    {l u : ℝ} (hlu : l ≤ u) (F : ℝ → ℝ)
    (hi : IntervalIntegrable F MeasureTheory.volume l u)
    (hn : ∀ y ∈ Set.Icc l u, 0 ≤ F y)
    (hab : ∀ i ∈ t, a i ≤ b i)
    (hsub : ∀ i ∈ t, Set.Ioc (a i) (b i) ⊆ Set.Ioc l u)
    (hd : (↑t : Set ℕ).Pairwise (Function.onFun Disjoint (fun i => Set.Ioc (a i) (b i)))) :
    (∑ i ∈ t, ∫ y in (a i)..(b i), F y) ≤ ∫ y in l..u, F y := by
  have hs : (⋃ i ∈ t, Set.Ioc (a i) (b i)) ⊆ Set.Ioc l u := by
    intro y hy
    obtain ⟨i, hy⟩ := Set.mem_iUnion.mp hy
    obtain ⟨hit, hy⟩ := Set.mem_iUnion.mp hy
    exact hsub i hit hy
  have hn' : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc l u)] F := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
    exact hn y (Set.Ioc_subset_Icc_self hy)
  calc
    _ = ∑ i ∈ t, ∫ y in Set.Ioc (a i) (b i), F y := by
      apply Finset.sum_congr rfl
      intro i hit
      exact intervalIntegral.integral_of_le (hab i hit)
    _ = ∫ y in ⋃ i ∈ t, Set.Ioc (a i) (b i), F y :=
      (MeasureTheory.integral_biUnion_finset t (fun _ _ => measurableSet_Ioc) hd
        (fun i hit => hi.1.mono_set (hsub i hit))).symm
    _ ≤ ∫ y in Set.Ioc l u, F y := MeasureTheory.setIntegral_mono_set hi.1 hn'
      (Filter.Eventually.of_forall hs)
    _ = _ := (intervalIntegral.integral_of_le hlu).symm


theorem block_moment_lower {Y Q : ℝ} {L : ℕ}
    (hY : 0 < Y) (hL4 : 4 ≤ L) (hQ : 2 ≤ Q)
    (hQL : 8 * Q ≤ (L : ℝ)) (hLY : 16 * (L : ℝ) ≤ Y) :
    Q ^ 2 * Y / 128 ≤
      ∫ y in (Y / 2)..(3 * Y),
        ‖Task387.windowSum (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊)
          (fun m => (blockSign L m : ℂ)) (Q / Y) y‖ ^ 2 := by
  let A : ℕ := ⌈Y / (L : ℝ)⌉₊
  let k : ℕ := ⌊Y / (4 * (L : ℝ))⌋₊
  let a : ℕ → ℝ := fun i => ((A + i : ℕ) : ℝ) * L + 1
  let b : ℕ → ℝ := fun i => ((A + i : ℕ) : ℝ) * L + (L : ℝ) / 2
  let S := Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊
  let F : ℝ → ℝ := fun y => ‖Task387.windowSum S (fun m => (blockSign L m : ℂ)) (Q / Y) y‖ ^ 2
  have hL : 0 < L := by omega
  have hLreal : (4 : ℝ) ≤ L := by exact_mod_cast hL4
  have hi (c d : ℝ) : IntervalIntegrable F MeasureTheory.volume c d :=
    Task308.window_sum_sq_intervalIntegrable S (fun m => (blockSign L m : ℂ)) (Q / Y) c d
  have hpos (i : ℕ) (hit : i ∈ Finset.range k) :
      Y ≤ ((A + i : ℕ) : ℝ) * L ∧ b i ≤ 3 * Y / 2 :=
    safe_block_positions hY hL hLY i (Finset.mem_range.mp hit)
  have hab (i : ℕ) (hit : i ∈ Finset.range k) : a i ≤ b i := by
    dsimp [a, b]
    linarith
  have hsub (i : ℕ) (hit : i ∈ Finset.range k) : Set.Ioc (a i) (b i) ⊆ Set.Ioc (Y / 2) (3 * Y) := by
    intro y hy
    have hh := hpos i hit
    have ha : Y + 1 ≤ a i := by dsimp [a]; linarith [hh.1]
    exact ⟨by linarith [hy.1], by linarith [hy.2, hh.2]⟩
  have hlower (i : ℕ) (hit : i ∈ Finset.range k) :
      ((L : ℝ) / 2 - 1) * (Q ^ 2 / 4) ≤ ∫ y in (a i)..(b i), F y := by
    have hh := hpos i hit
    have hmono := intervalIntegral.integral_mono_on (hab i hit)
      (intervalIntegrable_const (c := Q ^ 2 / 4)) (hi (a i) (b i)) (fun y hy => ?_)
    · calc
        _ = ∫ _y in (a i)..(b i), Q ^ 2 / 4 := by
          rw [intervalIntegral.integral_const]
          simp only [smul_eq_mul]
          dsimp [a, b]
          ring
        _ ≤ _ := hmono
    · have hn := safe_block_window_lower hY hL hQ hQL hLY hh.1 hh.2 hy
      have hq0 : 0 ≤ Q / 2 := by linarith
      have hs := pow_le_pow_left₀ hq0 hn 2
      dsimp [F, S]
      nlinarith
  have hd : (↑(Finset.range k) : Set ℕ).Pairwise
      (Function.onFun Disjoint (fun i => Set.Ioc (a i) (b i))) := by
    intro i hi j hj hij
    exact safe_block_intervals_disjoint A hL hij
  have hupper := disjoint_interval_integrals_le (Finset.range k) a b
    (show Y / 2 ≤ 3 * Y by linarith) F (hi _ _) (fun y hy => by dsimp [F]; positivity)
      hab hsub hd
  have hsum : (k : ℝ) * ((L : ℝ) / 2 - 1) * (Q ^ 2 / 4) ≤
      ∑ i ∈ Finset.range k, ∫ y in (a i)..(b i), F y := by
    calc
      _ = ∑ _i ∈ Finset.range k, ((L : ℝ) / 2 - 1) * (Q ^ 2 / 4) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun i hit => hlower i hit)
  have hm := mul_le_mul_of_nonneg_right (safe_block_mass_lower hY hL4 hLY)
    (show 0 ≤ Q ^ 2 / 4 by positivity)
  calc
    _ = (Y / 32) * (Q ^ 2 / 4) := by ring
    _ ≤ (k : ℝ) * ((L : ℝ) / 2 - 1) * (Q ^ 2 / 4) := hm
    _ ≤ ∑ i ∈ Finset.range k, ∫ y in (a i)..(b i), F y := hsum
    _ ≤ _ := hupper


theorem sieveQ_eventually_two {ε : ℝ} (hθ : 0 < 11 / 20 + ε) :
    ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ sieveQ ε x := by
  let γ : ℝ := 1 / 16 - 1 / 10 ^ 5
  have hγ : 0 < γ := by dsimp [γ]; norm_num
  have hp : ∀ᶠ x : ℝ in Filter.atTop, 4 ≤ x ^ ((11 / 20 + ε) * γ) :=
    (tendsto_rpow_atTop (mul_pos hθ hγ)).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [hp, Filter.eventually_gt_atTop (0 : ℝ)] with x hxp hx
  unfold sieveQ
  apply Nat.le_floor
  have he : (((x ^ (11 / 20 + ε)) ^ (2 * γ)) ^ (1 / 2 : ℝ)) =
      x ^ ((11 / 20 + ε) * γ) := by
    rw [← Real.rpow_mul (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le]
    congr 1
    ring
  change (2 : ℝ) ≤ (((x ^ (11 / 20 + ε)) ^ (2 * γ)) ^ (1 / 2 : ℝ)) / 2
  rw [he]
  linarith


theorem block_scales_eventually {ε : ℝ} (hθ : 0 < 11 / 20 + ε) :
    ∀ᶠ x : ℝ in Filter.atTop,
      0 < x ∧ 4 ≤ ⌊x ^ ((11 / 20 + ε) / 2)⌋₊ ∧ 2 ≤ sieveQ ε x ∧
      8 * (sieveQ ε x : ℝ) ≤ (⌊x ^ ((11 / 20 + ε) / 2)⌋₊ : ℝ) ∧
      16 * (⌊x ^ ((11 / 20 + ε) / 2)⌋₊ : ℝ) ≤ x ^ (11 / 20 + ε) := by
  let s : ℝ := (11 / 20 + ε) / 2
  have hs : 0 < s := by dsimp [s]; linarith
  have hr : ∀ᶠ x : ℝ in Filter.atTop, 32 ≤ x ^ s :=
    (tendsto_rpow_atTop hs).eventually (Filter.eventually_ge_atTop 32)
  have he : 0 < 7 * (11 / 20 + ε) / 16 := by positivity
  have ht : ∀ᶠ x : ℝ in Filter.atTop,
      x ^ (-(7 * (11 / 20 + ε) / 16)) < (1 / 16 : ℝ) :=
    (tendsto_rpow_neg_atTop he).eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hr, ht, sieveQ_eventually_two hθ,
    Filter.eventually_gt_atTop (0 : ℝ)] with x hR32 hratio hQ2 hx0
  let R : ℝ := x ^ s
  let Y : ℝ := x ^ (11 / 20 + ε)
  let L : ℕ := ⌊R⌋₊
  have hR : 32 ≤ R := hR32
  have hR0 : 0 < R := by linarith
  have hY : Y = R ^ 2 := by
    dsimp [Y, R]
    rw [← Real.rpow_mul_natCast hx0.le]
    congr 1
    dsimp [s]
    ring
  have hY1 : 1 ≤ Y := by rw [hY]; nlinarith
  have hQup := DecompC165b.sieveQ_le_sixteenth_power hY1
  have hpow : Y ^ (1 / 16 : ℝ) = x ^ ((11 / 20 + ε) / 16) := by
    dsimp [Y]
    rw [← Real.rpow_mul hx0.le]
    congr 1
    ring
  rw [hpow] at hQup
  have hid : x ^ ((11 / 20 + ε) / 16) =
      R * x ^ (-(7 * (11 / 20 + ε) / 16)) := by
    dsimp [R]
    rw [← Real.rpow_add hx0]
    congr 1
    dsimp [s]
    ring
  have hQR : (sieveQ ε x : ℝ) < R / 16 := by
    apply hQup.trans_lt
    rw [hid]
    convert mul_lt_mul_of_pos_left hratio hR0 using 1 <;> ring
  have hL4 : 4 ≤ L := Nat.le_floor (by simpa using (show (4 : ℝ) ≤ R by linarith))
  have hfloor : R < (L : ℝ) + 1 := Nat.lt_floor_add_one R
  have hLle : (L : ℝ) ≤ R := Nat.floor_le hR0.le
  have hQL : 8 * (sieveQ ε x : ℝ) ≤ (L : ℝ) := by linarith
  have hLY : 16 * (L : ℝ) ≤ Y := by rw [hY]; nlinarith
  exact ⟨hx0, hL4, hQ2, hQL, hLY⟩


theorem blockFamily_not_moment {ε : ℝ} (hθ : 0 < 11 / 20 + ε) :
    ¬ Task308.ShortMeanSquare ε 0 (blockFamily ε) := by
  intro hm
  obtain ⟨C, hC⟩ := LeanLab.BHP1997.DecompC165d.short_moment_principal_log_saving hm 1 (by norm_num)
  have ht : ∀ᶠ x : ℝ in Filter.atTop, 128 * (|C| + 1) < Real.log x :=
    Real.tendsto_log_atTop.eventually (Filter.eventually_gt_atTop _)
  obtain ⟨x, hxC, hsc, hlogbig⟩ :=
    ((Filter.eventually_ge_atTop C).and ((block_scales_eventually hθ).and ht)).exists
  obtain ⟨hx0, hL4, hQ2, hQL, hLY⟩ := hsc
  let Y : ℝ := x ^ (11 / 20 + ε)
  let Q : ℝ := sieveQ ε x
  let L : ℕ := ⌊x ^ ((11 / 20 + ε) / 2)⌋₊
  have hY : 0 < Y := Real.rpow_pos_of_pos hx0 _
  have hQ : (2 : ℝ) ≤ Q := by dsimp [Q]; exact_mod_cast hQ2
  have hscale : 0 < Q ^ 2 * Y := by positivity
  have hl := block_moment_lower hY hL4 hQ hQL hLY
  have hu := hC x hxC (show 1 ≤ sieveQ ε x by omega)
  have hχ : ∀ m : ℕ, (1 : DirichletCharacter ℂ 1) (m : ZMod 1) = 1 := by
    intro m
    rw [Subsingleton.elim (m : ZMod 1) 1, map_one]
  simp only [Complex.ofReal_zero, mul_zero, zero_div, sub_zero, hχ, mul_one] at hu
  change (∫ y in (Y / 2)..(3 * Y),
      ‖Task387.windowSum (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊)
        (fun m => (blockSign L m : ℂ)) (Q / Y) y‖ ^ 2) ≤
          C * Q ^ 2 * Y * Real.log x ^ (-1 : ℝ) at hu
  have hh : (Q ^ 2 * Y) * (1 / 128 : ℝ) ≤
      (Q ^ 2 * Y) * (C * Real.log x ^ (-1 : ℝ)) := by
    convert hl.trans hu using 1 <;> ring
  have hc : (1 / 128 : ℝ) ≤ C * Real.log x ^ (-1 : ℝ) :=
    (mul_le_mul_iff_right₀ hscale).mp hh
  have hlog : 0 < Real.log x := by nlinarith [abs_nonneg C]
  rw [Real.rpow_neg hlog.le, Real.rpow_one, ← div_eq_mul_inv] at hc
  have hc' := (le_div_iff₀ hlog).mp hc
  linarith [le_abs_self C]

theorem centered_to_moment_transfer_false {ε : ℝ} (hθ : 0 < 11 / 20 + ε) :
    ∃ b : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ (0 : ℝ)) ∧
      Task308.ShortDistribution ε 0 b ∧ ¬ Task308.ShortMeanSquare ε 0 b := by
  exact ⟨blockFamily ε, blockFamily_divisor_bound ε, blockFamily_distribution hθ,
    blockFamily_not_moment hθ⟩



/-- Pages 3 and 52. CONDITIONAL on the original cited Theorem 4 and Lemma 9.
This negates the full type of the sealed exceptional leaf, with the two exact
short-condition predicates folded. The counterexample itself uses neither
cited input. This is a mismatch of the split statement, not a paper error. -/
theorem sealed_exceptional_leaf_type_false
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ¬ (Thm4.Theorem4Paper → MeanValue132.Lemma9 →
      ∀ {ω : ℝ → ℝ},
        LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω →
        LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω →
        ∀ {B ε v0 : ℝ}, 0 < ε → ε ≤ 1 / 10 ^ 8 →
          ∀ {b0 : ℝ → ℕ → ℝ},
            (∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
            Task308.ShortDistribution ε v0 b0 → Task308.ShortMeanSquare ε v0 b0) := by
  intro hleaf
  obtain ⟨ω, hω, hz⟩ := leaf_buchstab_model_exists
  let ε : ℝ := 1 / 200000000
  have hε : 0 < ε := by norm_num [ε]
  have hε8 : ε ≤ 1 / 10 ^ 8 := by norm_num [ε]
  have hθ : 0 < 11 / 20 + ε := by norm_num [ε]
  have hm : Task308.ShortMeanSquare ε 0 (blockFamily ε) :=
    hleaf h4 h9 (ω := ω) hω hz (B := 0) (ε := ε) (v0 := 0) hε hε8
      (b0 := blockFamily ε) (blockFamily_divisor_bound ε) (blockFamily_distribution hθ)
  exact blockFamily_not_moment hθ hm

end BlockDiagnostic479

end LeanLab.BHP1997.DecompC165d

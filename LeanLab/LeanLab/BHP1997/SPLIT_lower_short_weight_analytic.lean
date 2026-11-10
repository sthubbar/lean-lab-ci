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
  sorry

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

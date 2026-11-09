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

Every leaf is OPEN. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165d

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
  have hε55 : ε < 9 / 20 := by linarith
  have hrc0 : RightConditions ε B 0 (fun _ _ => 0) :=
    InstancesC165.right_conditions_zero hB
  have hv0_le : v0 ≤ 0 :=
    DecompC165b.right_density_mono (by linarith) hε55 hrc hrc0 hnonpos
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
`v0 = 0` the family `b0 = 0` satisfies the divisor bound and the mean value, so neither the
hypotheses nor the conclusion degenerate. -/
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

end LeanLab.BHP1997.DecompC165d

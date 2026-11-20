import LeanLab.Ported.Prove2Me.Decomp587lR0J16
import LeanLab.ChenDoubleSieve.Task587R0J17
import LeanLab.ChenDoubleSieve.Task587R0J19

/-!
Ordered cell bridges for Wu 2004 page 26, D2,17 and D2,19.
The parameters are Table 1 row 1 page 30.
The verifier comes from Prove2Me mission 1e48f99d, author kmehltretter82,
Apache 2.0, accepted proof LL_Decomp587l.r0j16_short.
AI wrote the new bridges, certificate generators and interval assemblies.
Binary Goldbach is open.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task661
open Wu04Functional Task587
open LeanLab.Ported.Prove2Me.R0J16.SolBuchstabR0J16

def j17Cell : Cell4 := .c31 A_num B_num B_num 1646784
def j19Cell : Cell4 := .c13 1026304 A_num B_num 1646784

def checkJ17 (pa pb : Nat) (t : CTree) : Bool :=
  match evalTree pa pb t j17Cell with
  | some v => Nat.ble v 183164000
  | none => false

def checkJ19 (pa pb : Nat) (t : CTree) : Bool :=
  match evalTree pa pb t j19Cell with
  | some v => Nat.ble v 70737000
  | none => false

/-- A measure preserving coordinate map transports any ordered domain into a cell. -/
theorem integral_le_cell {ω : ℝ → ℝ} (φ : ℝ) {lo hi : Fin 4 → ℝ} {c : Cell4}
    (hInt : IntegrableOn (integrand4 ω φ) c.set volume)
    (hn : ∀ x ∈ c.set, 0 ≤ integrand4 ω φ x)
    (hsub : ∀ x ∈ domain lo hi, (x 0, x 1, x 2, x 3) ∈ c.set) :
    buchstabIntegral ω 2 lo hi φ ≤ ∫ x in c.set, integrand4 ω φ x := by
  let e3 : (Fin 3 → ℝ) ≃ᵐ (ℝ × ℝ × ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.finTwoArrow (α := ℝ)))
  let e4 : (Fin 4 → ℝ) ≃ᵐ R4 :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) e3)
  have hmp3 : MeasurePreserving e3 volume volume := by
    have h1 := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
    have h2 : MeasurePreserving
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.finTwoArrow (α := ℝ)))
        (volume.prod volume) (volume.prod (volume.prod volume)) :=
      (MeasurePreserving.id volume).prod (MeasureTheory.volume_preserving_finTwoArrow ℝ)
    exact h2.comp h1
  have hmp : MeasurePreserving e4 volume volume := by
    have h1 := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0
    have h2 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) e3)
        (volume.prod volume) (volume.prod volume) :=
      (MeasurePreserving.id volume).prod hmp3
    exact h2.comp h1
  have he4_apply : ∀ x : Fin 4 → ℝ, e4 x = (x 0, x 1, x 2, x 3) := fun _ => rfl
  have hfun : (fun x : Fin 4 → ℝ =>
      ω ((φ - ∑ j, x j) / x ⟨2, by omega⟩) / ((∏ j, x j) * x ⟨2, by omega⟩)) =
      (fun x : Fin 4 → ℝ => integrand4 ω φ (e4 x)) := by
    ext x
    simp only [integrand4, he4_apply, Fin.sum_univ_four, Fin.prod_univ_four]
    have hnum : (φ - (x 0 + x 1 + x 2 + x 3)) / x ⟨2, by omega⟩ =
        (φ - (x 0 + x 1 + x 2 + x 3)) / x 2 := rfl
    have hden : (x 0 * x 1 * x 2 * x 3) * x ⟨2, by omega⟩ = x 0 * x 1 * x 2 * x 2 * x 3 := by
      change (x 0 * x 1 * x 2 * x 3) * x 2 = x 0 * x 1 * x 2 * x 2 * x 3
      ring
    rw [hnum, hden]
  have hi' : IntegrableOn (fun x : Fin 4 → ℝ => integrand4 ω φ (e4 x)) (e4 ⁻¹' c.set) volume :=
    (hmp.integrableOn_comp_preimage e4.measurableEmbedding).2 hInt
  have hn' : 0 ≤ᵐ[volume.restrict (e4 ⁻¹' c.set)] (fun x => integrand4 ω φ (e4 x)) := by
    filter_upwards [ae_restrict_mem ((Cell4.measurableSet_set c).preimage e4.measurable)] with x hx
    exact hn (e4 x) hx
  have hs : domain lo hi ⊆ e4 ⁻¹' c.set := by
    intro x hx
    simpa only [mem_preimage, he4_apply] using hsub x hx
  unfold buchstabIntegral
  rw [hfun]
  calc
    (∫ x in domain lo hi, integrand4 ω φ (e4 x)) ≤
        ∫ x in e4 ⁻¹' c.set, integrand4 ω φ (e4 x) :=
      setIntegral_mono_set hi' hn' (Filter.Eventually.of_forall hs)
    _ = ∫ x in c.set, integrand4 ω φ x :=
      hmp.setIntegral_preimage_emb e4.measurableEmbedding (integrand4 ω φ) c.set

/-- The exact D2,17 domain lies in its outward grid enclosure. -/
theorem j17_domain_subset (x : Fin 4 → ℝ)
    (hx : x ∈ domain (fun j => (r0j17_lo j : ℝ)) (fun j => (r0j17_hi j : ℝ))) :
    (x 0, x 1, x 2, x 3) ∈ j17Cell.set := by
  rcases hx with ⟨hm, hb⟩
  have h0 := (hb 0).1
  have h2 := (hb 2).2
  have h3 := hb 3
  norm_num [r0j17_lo, r0j17_hi] at h0 h2 h3
  have ha : gval A_num = (10 / 29 : ℝ) := by norm_num [gval, A_num, D_grid]
  have hb' : gval B_num = (25 / 61 : ℝ) := by norm_num [gval, B_num, D_grid]
  have hc : (5 / 11 : ℝ) ≤ gval 1646784 := by norm_num [gval, D_grid]
  change gval A_num ≤ x 0 ∧ x 0 ≤ x 1 ∧ x 1 ≤ x 2 ∧ x 2 ≤ gval B_num ∧
    gval B_num ≤ x 3 ∧ x 3 ≤ gval 1646784
  rw [ha, hb']
  exact ⟨h0, hm (by decide : (0 : Fin 4) ≤ 1), hm (by decide : (1 : Fin 4) ≤ 2),
    h2, h3.1, h3.2.trans hc⟩

/-- The exact D2,19 domain lies in its outward grid enclosure. -/
theorem j19_domain_subset (x : Fin 4 → ℝ)
    (hx : x ∈ domain (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ))) :
    (x 0, x 1, x 2, x 3) ∈ j19Cell.set := by
  rcases hx with ⟨hm, hb⟩
  have h0 := hb 0
  have h1 := (hb 1).1
  have h3 := (hb 3).2
  norm_num [r0j19_lo, r0j19_hi] at h0 h1 h3
  have ha : gval A_num = (10 / 29 : ℝ) := by norm_num [gval, A_num, D_grid]
  have hb' : gval B_num = (25 / 61 : ℝ) := by norm_num [gval, B_num, D_grid]
  have hl : gval 1026304 ≤ (100 / 353 : ℝ) := by norm_num [gval, D_grid]
  have hu : (5 / 11 : ℝ) ≤ gval 1646784 := by norm_num [gval, D_grid]
  change gval 1026304 ≤ x 0 ∧ x 0 ≤ gval A_num ∧ gval B_num ≤ x 1 ∧
    x 1 ≤ x 2 ∧ x 2 ≤ x 3 ∧ x 3 ≤ gval 1646784
  rw [ha, hb']
  exact ⟨hl.trans h0.1, h0.2, h1, hm (by decide : (1 : Fin 4) ≤ 2),
    hm (by decide : (2 : Fin 4) ≤ 3), h3.trans hu⟩

/-- An accepted tree bounds D2,17 throughout the certified phi interval. -/
theorem j17_interval_bound {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {pa pb : Nat} {t : CTree} {φ : ℝ}
    (hpa : (pa : ℝ) / D_grid ≤ φ) (hpb : φ ≤ (pb : ℝ) / D_grid)
    (hchk : checkJ17 pa pb t = true) :
    buchstabIntegral ω 2 (fun j => (r0j17_lo j : ℝ)) (fun j => (r0j17_hi j : ℝ)) φ ≤
      ((45791 / 250000000) : ℝ) := by
  unfold checkJ17 at hchk
  cases heval : evalTree pa pb t j17Cell with
  | none => rw [heval] at hchk; cases hchk
  | some v =>
    rw [heval] at hchk
    have hv : v ≤ 183164000 := Nat.ble_eq.mp hchk
    have hb := evalTree_sound hω hz hpa hpb t j17Cell (by norm_num [j17Cell, A_num, B_num]) heval
    have hr : (v : ℝ) / S_scale ≤ ((45791 / 250000000) : ℝ) := by
      calc
        (v : ℝ) / S_scale ≤ (183164000 : ℝ) / S_scale :=
          div_le_div_of_nonneg_right (by exact_mod_cast hv) (by norm_num [S_scale])
        _ = ((45791 / 250000000) : ℝ) := by norm_num [S_scale]
    exact (integral_le_cell (c := j17Cell) φ
      (integrand4_integrableOn hω hz φ (c := j17Cell) (by norm_num [j17Cell, A_num, B_num]))
      (integrand4_nonneg hω hz φ (c := j17Cell) (by norm_num [j17Cell, A_num, B_num])) j17_domain_subset).trans (hb.trans hr)

/-- An accepted tree bounds D2,19 throughout the certified phi interval. -/
theorem j19_interval_bound {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {pa pb : Nat} {t : CTree} {φ : ℝ}
    (hpa : (pa : ℝ) / D_grid ≤ φ) (hpb : φ ≤ (pb : ℝ) / D_grid)
    (hchk : checkJ19 pa pb t = true) :
    buchstabIntegral ω 2 (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ)) φ ≤
      ((70737 / 1000000000) : ℝ) := by
  unfold checkJ19 at hchk
  cases heval : evalTree pa pb t j19Cell with
  | none => rw [heval] at hchk; cases hchk
  | some v =>
    rw [heval] at hchk
    have hv : v ≤ 70737000 := Nat.ble_eq.mp hchk
    have hb := evalTree_sound hω hz hpa hpb t j19Cell (by norm_num [j19Cell, A_num, B_num]) heval
    have hr : (v : ℝ) / S_scale ≤ ((70737 / 1000000000) : ℝ) := by
      calc
        (v : ℝ) / S_scale ≤ (70737000 : ℝ) / S_scale :=
          div_le_div_of_nonneg_right (by exact_mod_cast hv) (by norm_num [S_scale])
        _ = ((70737 / 1000000000) : ℝ) := by norm_num [S_scale]
    exact (integral_le_cell (c := j19Cell) φ
      (integrand4_integrableOn hω hz φ (c := j19Cell) (by norm_num [j19Cell, A_num, B_num]))
      (integrand4_nonneg hω hz φ (c := j19Cell) (by norm_num [j19Cell, A_num, B_num])) j19_domain_subset).trans (hb.trans hr)

end LeanLab.ChenDoubleSieve.Task661

#print axioms LeanLab.ChenDoubleSieve.Task661.integral_le_cell
#print axioms LeanLab.ChenDoubleSieve.Task661.j17_domain_subset
#print axioms LeanLab.ChenDoubleSieve.Task661.j19_domain_subset
#print axioms LeanLab.ChenDoubleSieve.Task661.j17_interval_bound
#print axioms LeanLab.ChenDoubleSieve.Task661.j19_interval_bound

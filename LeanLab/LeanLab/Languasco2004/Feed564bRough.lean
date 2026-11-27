/-
Jia 1996 Lemma 27, pages 280 to 282, with Lemma 21 on page 262 and display 40 on page 261.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
Split of Decomp564b.rough11_to_integral into cited LEAF steps, burst-20261122.
The parent statement is proved below from the leaves, CONDITIONAL ON the open leaves
and on nothing else; the numerical value of integral11 is not used here.
-/
import LeanLab.Languasco2004.Model564
import LeanLab.Languasco2004.Integral564
import LeanLab.Languasco2004.Decomp578e
import LeanLab.Languasco2004.Decomp578c
import LeanLab.Languasco2004.Sieve565

namespace LeanLab.Languasco2004.Feed564bRough
open Finset Real Decomp279a Decomp316c Model564 RemainderData564 Integral564
open BuchstabInitial316 Kernel548 MovingIntegral548
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Pages 281 and 282: the full Buchstab kernel integral on printed subdomain i.
The same expression as Buchstab564.buchstabRow, restated here so that this module avoids
the Numeric564 import chain, whose Polynomial564s13 is killed for memory in the container. -/
def fullRow (w : ℝ → ℝ) (i : Fin 16) : ℝ :=
  let r := numericData i
  ∫ t in (r 0 : ℝ)..(r 1),
    ∫ u in ((r 2 : ℝ)+r 3*t)..((r 4 : ℝ)+r 5*t),
      w ((1-t-u)/u) / (t*u^2)

/-- Pages 261, 281 and 282: the full kernel is continuous on the common rectangle.
Same proof as Buchstab564.full_kernel_continuousOn. -/
theorem full_kernel_continuousOn' (w : ℝ → ℝ) (hw : ContinuousOn w (Set.Ici 1)) :
    ContinuousOn (fun z : ℝ × ℝ => w ((1-z.1-z.2)/z.2) / (z.1*z.2^2))
      (Set.Icc (1/3:ℝ) (1/2) ×ˢ Set.Icc (1/10:ℝ) (1/5)) := by
  let R := Set.Icc (1/3:ℝ) (1/2) ×ˢ Set.Icc (1/10:ℝ) (1/5)
  have ht (z : ℝ × ℝ) (hz : z ∈ R) : 0 < z.1 := by linarith [hz.1.1]
  have hu (z : ℝ × ℝ) (hz : z ∈ R) : 0 < z.2 := by linarith [hz.2.1]
  have ha (z : ℝ × ℝ) (hz : z ∈ R) : 1 ≤ (1-z.1-z.2)/z.2 := by
    apply (le_div_iff₀ (hu z hz)).mpr
    linarith [hz.1.2, hz.2.2]
  have hc : ContinuousOn (fun z : ℝ × ℝ => (1-z.1-z.2)/z.2) R :=
    ((continuousOn_const.sub continuous_fst.continuousOn).sub continuous_snd.continuousOn).div
      continuous_snd.continuousOn (fun z hz => (hu z hz).ne')
  exact (hw.comp hc (fun z hz => ha z hz)).div (by fun_prop)
    (fun z hz => (mul_pos (ht z hz) (sq_pos_of_pos (hu z hz))).ne')

/-- Pages 281 and 282: the full kernel inner integral is continuous.
Same proof as Buchstab564.full_inner_continuousOn. -/
theorem full_inner_continuousOn' (w : ℝ → ℝ) (hw : ContinuousOn w (Set.Ici 1)) (i : Fin 16) :
    let r := numericData i
    ContinuousOn (fun t : ℝ => ∫ u in ((r 2 : ℝ)+r 3*t)..((r 4 : ℝ)+r 5*t),
      w ((1-t-u)/u) / (t*u^2)) (Set.Icc (r 0 : ℝ) (r 1)) := by
  dsimp
  have hab : (numericData i 0 : ℝ) ≤ numericData i 1 := by
    fin_cases i <;> norm_num [numericData]
  have hF : ContinuousOn (fun z : ℝ × ℝ => w ((1-z.1-z.2)/z.2) / (z.1*z.2^2))
      (Set.Icc (numericData i 0 : ℝ) (numericData i 1) ×ˢ Set.Icc (1/10:ℝ) (1/5)) := by
    apply (full_kernel_continuousOn' w hw).mono
    intro z hz
    obtain ⟨ht, ht', _⟩ := row_endpoints i z.1 hz.1.1 hz.1.2
    exact ⟨⟨ht,ht'⟩,hz.2⟩
  apply moving_integral_continuousOn
    (fun t u : ℝ => w ((1-t-u)/u) / (t*u^2))
    (numericData i 0) (numericData i 1) (1/10) (1/5)
    (fun t => (numericData i 2 : ℝ)+numericData i 3*t)
    (fun t => (numericData i 4 : ℝ)+numericData i 5*t)
    hab (by norm_num) hF (by fun_prop) (by fun_prop)
  intro t ht
  obtain ⟨_, _, hl, hlu, hu⟩ := row_endpoints i t ht.1 ht.2
  exact ⟨hl, hlu.trans hu, hl.trans hlu, hu⟩

/-- Pages 261, 281 and 282: the source lower kernel is below the full kernel.
Same proof as Buchstab564.row_kernel_buchstab_lower. -/
theorem row_kernel_lower' (w : ℝ → ℝ)
    (hinit : ∀ s : ℝ, 2 ≤ s → s ≤ 3 → w s = buchstabInitial s)
    (hglobal : ∀ s : ℝ, 3 ≤ s → 0.5607 ≤ w s)
    (i : Fin 16) (t u : ℝ)
    (htl : (numericData i 0 : ℝ) ≤ t) (htu : t ≤ (numericData i 1 : ℝ))
    (hul : (numericData i 2 : ℝ)+numericData i 3*t ≤ u)
    (huu : u ≤ (numericData i 4 : ℝ)+numericData i 5*t) :
    kernel i t u ≤ w ((1-t-u)/u) / (t*u^2) := by
  obtain ⟨ht, hu, hv, _⟩ := row_kernel_bounds i t u htl htu hul huu
  have hr := row_buchstab_range i t u htl htu hul huu
  by_cases hk : isLog i = true
  · simp only [hk, ↓reduceIte] at hr
    rw [hinit _ hr.1 hr.2]
    simpa only [kernel, hk, ↓reduceIte] using
      (initial_kernel_high t u ht hu hv hr.1).ge
  · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hr
    simpa only [kernel, hk, Bool.false_eq_true, ↓reduceIte] using
      div_le_div_of_nonneg_right (hglobal _ hr) (mul_pos ht (sq_pos_of_pos hu)).le

/-- Pages 281 and 282: each printed lower integral is below the full Buchstab row integral.
Same proof as Buchstab564.row_integral_buchstab_lower. -/
theorem row_integral_lower' (w : ℝ → ℝ) (hw : ContinuousOn w (Set.Ici 1))
    (hinit : ∀ s : ℝ, 2 ≤ s → s ≤ 3 → w s = buchstabInitial s)
    (hglobal : ∀ s : ℝ, 3 ≤ s → 0.5607 ≤ w s) (i : Fin 16) :
    sourceIntegral i ≤ fullRow w i := by
  dsimp [sourceIntegral, fullRow]
  have hab : (numericData i 0 : ℝ) ≤ numericData i 1 := by
    fin_cases i <;> norm_num [numericData]
  apply intervalIntegral.integral_mono_on hab
    ((source_inner_continuousOn i).intervalIntegrable_of_Icc hab)
    ((full_inner_continuousOn' w hw i).intervalIntegrable_of_Icc hab)
  intro t ht
  obtain ⟨ht1, ht2, hl, hlu, hu⟩ := row_endpoints i t ht.1 ht.2
  have hk : ContinuousOn (kernel i t) (Set.Icc ((numericData i 2 : ℝ)+numericData i 3*t)
      ((numericData i 4 : ℝ)+numericData i 5*t)) :=
    (kernel_continuousOn i).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu' => ⟨⟨ht1,ht2⟩,⟨hl.trans hu'.1,hu'.2.trans hu⟩⟩)
  have hf : ContinuousOn (fun u : ℝ => w ((1-t-u)/u) / (t*u^2))
      (Set.Icc ((numericData i 2 : ℝ)+numericData i 3*t)
      ((numericData i 4 : ℝ)+numericData i 5*t)) :=
    (full_kernel_continuousOn' w hw).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu' => ⟨⟨ht1,ht2⟩,⟨hl.trans hu'.1,hu'.2.trans hu⟩⟩)
  apply intervalIntegral.integral_mono_on hlu (hk.intervalIntegrable_of_Icc hlu)
    (hf.intervalIntegrable_of_Icc hlu)
  intro u hu'
  exact row_kernel_lower' w hinit hglobal i t u ht.1 ht.2 hu'.1 hu'.2

/-- Jia page 261 display 40 and page 262 Lemma 21: the defining properties of the
Buchstab function, continuity from one, the value 1/u on one to two, and the
delay integral equation u w u = 1 + integral of w from 1 to u - 1 for u at least two.
These are exactly the hypotheses of Decomp578c.lemma21_rough_asymptotic. -/
def IsBuchstab (w : ℝ → ℝ) : Prop :=
  ContinuousOn w (Set.Ici 1) ∧ (∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u) ∧
    (∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ s in (1 : ℝ)..(u - 1), w s)

/-- Jia page 280, the main term of the arithmetic B model after Lemma 21 on page 262:
each pair p, q of a source region contributes w of log t over log q times t over log q,
where t = Y / (p q) is the cofactor length. Same finite index set as roughModel. -/
def buchstabMain (labels : Finset ℕ) (w : ℝ → ℝ) (Y : ℝ) : ℝ :=
  ∑ p ∈ range (⌊2 * Y⌋₊ + 1), ∑ q ∈ range (⌊2 * Y⌋₊ + 1),
    if p.Prime ∧ q.Prime ∧ regionIndex Y p q ∈ labels then
      w (Real.log (Y / ((p : ℝ) * q)) / Real.log q) * ((Y / ((p : ℝ) * q)) / Real.log q)
    else 0

/-- Jia page 261 display 40: the Buchstab function exists, by the explicit construction
Buchstab578.buchstab_exists. -/
theorem isBuchstab_exists : ∃ w : ℝ → ℝ, IsBuchstab w :=
  Buchstab578.buchstab_exists

/-- Jia page 261 display 40 and page 262 Lemma 20: the global numerical lower bound
w s at least 0.5607 for every s at least three, by uniqueness Buchstab578.solution_eq_buchstab
and the grid propagation Decomp578e.global_three_from_grid. -/
theorem buchstab_global_lower (w : ℝ → ℝ) (hw : IsBuchstab w) :
    ∀ s : ℝ, 3 ≤ s → (0.5607 : ℝ) ≤ w s := by
  intro s hs
  rw [Buchstab578.solution_eq_buchstab w hw.2.1 hw.2.2 s (by linarith)]
  exact (Decomp578e.global_three_from_grid s hs).1

/-- Jia page 261 display 40: the delay equation gives the explicit second segment
w s = (1 + log (s - 1)) / s on two to three. -/
theorem buchstab_initial_segment (w : ℝ → ℝ) (hw : IsBuchstab w) :
    ∀ s : ℝ, 2 ≤ s → s ≤ 3 → w s = buchstabInitial s := by
  intro s hs2 hs3
  obtain ⟨_, h12, hdelay⟩ := hw
  have hd := hdelay s hs2
  have hint : (∫ x in (1 : ℝ)..(s - 1), w x) = ∫ x in (1 : ℝ)..(s - 1), x⁻¹ := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    rw [h12 x hx.1 (by linarith [hx.2]), one_div]
  rw [hint, integral_inv_of_pos (by norm_num) (by linarith), div_one] at hd
  rw [buchstabInitial_eq_log hs2]
  have hs0 : (0 : ℝ) < s := by linarith
  field_simp
  linarith

/-- LEAF: Jia pages 280 and 281 with Lemma 21 on page 262, applied to each cofactor count
S of B_pq and q over regions 33, 36, 38, 40, 42, 46 and 49, then summed; the Lemma 21 error
is absorbed by the Mertens bound for the sum of t over log q over these regions. HARD -/
theorem rough11_lemma21_sum (w : ℝ → ℝ) (hw : IsBuchstab w) (η : ℝ) (hη : 0 < η) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      buchstabMain labels11 w Y - η * (Y / Real.log Y) ≤ roughModel labels11 Y := by
  sorry

/-- LEAF: Jia pages 280 and 281, the prime number theorem Riemann sum step: the double prime
sum of the Lemma 21 main term over regions 33, 36, 38, 40, 42, 46 and 49 is at least the
Buchstab integral over the nine printed subdomains, rows two to ten, times Y over log Y. HARD -/
theorem buchstabMain11_riemann (w : ℝ → ℝ) (hw : IsBuchstab w) (η : ℝ) (hη : 0 < η) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ((∑ i ∈ (Finset.univ.filter (fun i : Fin 16 => i.val < 9)), fullRow w i) - η) *
        (Y / Real.log Y) ≤ buchstabMain labels11 w Y := by
  sorry

/-- Jia pages 280 and 281: generic assembly of a family transfer from a Buchstab lower
integral, the summed Lemma 21 step and the Riemann sum step. -/
theorem family_from_buchstab (labels : Finset ℕ) (I S : ℝ) (w : ℝ → ℝ) (hIS : I ≤ S)
    (h21 : ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      buchstabMain labels w Y - η * (Y / Real.log Y) ≤ roughModel labels Y)
    (hR : ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      (S - η) * (Y / Real.log Y) ≤ buchstabMain labels w Y)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → 2 ≤ Y →
      (I - δ) * Y / Real.log Y ≤ roughModel labels Y := by
  obtain ⟨Y1, h1⟩ := h21 (δ / 2) (by linarith)
  obtain ⟨Y2, h2⟩ := hR (δ / 2) (by linarith)
  refine ⟨max Y1 Y2, fun Y hY hY2 => ?_⟩
  have a := h1 Y ((le_max_left _ _).trans hY)
  have b := h2 Y ((le_max_right _ _).trans hY)
  have hq : 0 ≤ Y / Real.log Y := div_nonneg (by linarith) (Real.log_nonneg (by linarith))
  have c : (I - δ) * (Y / Real.log Y) ≤ (S - δ / 2) * (Y / Real.log Y) - δ / 2 * (Y / Real.log Y) := by
    nlinarith
  rw [mul_div_assoc]
  linarith

/-- Jia Lemma 27 pages 280 and 281: Decomp564b.rough11_to_integral from the leaves.
CONDITIONAL ON rough11_lemma21_sum and buchstabMain11_riemann. Same type as the parent. -/
theorem rough11_to_integral_from_leaves (δ : ℝ) (hδ : 0 < δ) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → 2 ≤ Y →
      (integral11 - δ) * Y / Real.log Y ≤ roughModel labels11 Y := by
  obtain ⟨w, hw⟩ := isBuchstab_exists
  have hrow : integral11 ≤
      ∑ i ∈ (Finset.univ.filter (fun i : Fin 16 => i.val < 9)), fullRow w i :=
    sum_le_sum fun i _ => row_integral_lower' w hw.1
      (buchstab_initial_segment w hw) (buchstab_global_lower w hw) i
  exact family_from_buchstab labels11 _ _ w hrow (rough11_lemma21_sum w hw)
    (buchstabMain11_riemann w hw) δ hδ

#print axioms full_kernel_continuousOn'
#print axioms full_inner_continuousOn'
#print axioms row_kernel_lower'
#print axioms row_integral_lower'
#print axioms isBuchstab_exists
#print axioms buchstab_global_lower
#print axioms buchstab_initial_segment
#print axioms rough11_lemma21_sum
#print axioms buchstabMain11_riemann
#print axioms family_from_buchstab
#print axioms rough11_to_integral_from_leaves
end
end LeanLab.Languasco2004.Feed564bRough
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
import LeanLab.Languasco2004.Feed564bPrime
import LeanLab.Languasco2004.Decomp578c

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

/-- Jia pages 267 to 269: the region data of the family give, in logarithmic form,
Y^(16/135) < q < p, p at most Y^(1/2) and p q^2 at most Y^(9/10). -/
theorem labels11_logs (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h : regionIndex Y p q ∈ labels11) :
    (16 / 135) * Real.log Y < Real.log q ∧ Real.log q < Real.log p ∧
      Real.log p ≤ (1 / 2) * Real.log Y ∧
      Real.log p + 2 * Real.log q ≤ (9 / 10) * Real.log Y := by
  have h0 : regionIndex Y p q ≠ 0 := by
    intro h0; rw [h0] at h; simp [labels11] at h
  obtain ⟨l1, l2, l3, l4⟩ := Feed564bPrime.region_logs Y hY p q hp hq h0
  have hL : 0 < Real.log Y := Real.log_pos hY
  generalize regionIndex Y p q = i at h l1 l2 l3 l4
  simp only [labels11, mem_insert, mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [show regionData 33 0 = (1649/4752 : ℚ) from rfl, show regionData 33 1 = (25/72 : ℚ) from rfl, show regionData 33 2 = (-70/59 : ℚ) from rfl, show regionData 33 3 = (34/59 : ℚ) from rfl, show regionData 33 4 = (-58/49 : ℚ) from rfl, show regionData 33 5 = (85/147 : ℚ) from rfl] at l1 l2 l3 l4
    push_cast at l1 l2 l3 l4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · simp only [show regionData 36 0 = (25/72 : ℚ) from rfl, show regionData 36 1 = (10/27 : ℚ) from rfl, show regionData 36 2 = (-70/59 : ℚ) from rfl, show regionData 36 3 = (34/59 : ℚ) from rfl, show regionData 36 4 = (-58/49 : ℚ) from rfl, show regionData 36 5 = (85/147 : ℚ) from rfl] at l1 l2 l3 l4
    push_cast at l1 l2 l3 l4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · simp only [show regionData 38 0 = (10/27 : ℚ) from rfl, show regionData 38 1 = (617/1620 : ℚ) from rfl, show regionData 38 2 = (-70/59 : ℚ) from rfl, show regionData 38 3 = (34/59 : ℚ) from rfl, show regionData 38 4 = (-58/49 : ℚ) from rfl, show regionData 38 5 = (85/147 : ℚ) from rfl] at l1 l2 l3 l4
    push_cast at l1 l2 l3 l4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · simp only [show regionData 40 0 = (617/1620 : ℚ) from rfl, show regionData 40 1 = (1823/4725 : ℚ) from rfl, show regionData 40 2 = (-70/59 : ℚ) from rfl, show regionData 40 3 = (34/59 : ℚ) from rfl, show regionData 40 4 = (-58/49 : ℚ) from rfl, show regionData 40 5 = (85/147 : ℚ) from rfl] at l1 l2 l3 l4
    push_cast at l1 l2 l3 l4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · simp only [show regionData 42 0 = (1823/4725 : ℚ) from rfl, show regionData 42 1 = (3041/7830 : ℚ) from rfl, show regionData 42 2 = (0 : ℚ) from rfl, show regionData 42 3 = (16/135 : ℚ) from rfl, show regionData 42 4 = (-58/49 : ℚ) from rfl, show regionData 42 5 = (85/147 : ℚ) from rfl] at l1 l2 l3 l4
    push_cast at l1 l2 l3 l4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · simp only [show regionData 46 0 = (11/27 : ℚ) from rfl, show regionData 46 1 = (34/81 : ℚ) from rfl, show regionData 46 2 = (-29/19 : ℚ) from rfl, show regionData 46 3 = (89/114 : ℚ) from rfl, show regionData 46 4 = (-35/23 : ℚ) from rfl, show regionData 46 5 = (18/23 : ℚ) from rfl] at l1 l2 l3 l4
    push_cast at l1 l2 l3 l4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · simp only [show regionData 49 0 = (34/81 : ℚ) from rfl, show regionData 49 1 = (49/114 : ℚ) from rfl, show regionData 49 2 = (-29/19 : ℚ) from rfl, show regionData 49 3 = (89/114 : ℚ) from rfl, show regionData 49 4 = (-35/23 : ℚ) from rfl, show regionData 49 5 = (18/23 : ℚ) from rfl] at l1 l2 l3 l4
    push_cast at l1 l2 l3 l4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Jia pages 267 to 269: the region data of the family give, in logarithmic form,
Y^(16/135) < q < p, p at most Y^(1/2) and p q^2 at most Y^(9/10). -/
theorem labels12_logs (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h : regionIndex Y p q ∈ labels12) :
    (16 / 135) * Real.log Y < Real.log q ∧ Real.log q < Real.log p ∧
      Real.log p ≤ (1 / 2) * Real.log Y ∧
      Real.log p + 2 * Real.log q ≤ (9 / 10) * Real.log Y := by
  have h0 : regionIndex Y p q ≠ 0 := by
    intro h0; rw [h0] at h; simp [labels12] at h
  obtain ⟨l1, l2, l3, l4⟩ := Feed564bPrime.region_logs Y hY p q hp hq h0
  have hL : 0 < Real.log Y := Real.log_pos hY
  generalize regionIndex Y p q = i at h l1 l2 l3 l4
  simp only [labels12, mem_insert, mem_singleton] at h
  rcases h with rfl | rfl
  · simp only [show regionData 53 0 = (3397/7830 : ℚ) from rfl, show regionData 53 1 = (4/9 : ℚ) from rfl, show regionData 53 2 = (-35/12 : ℚ) from rfl, show regionData 53 3 = (17/12 : ℚ) from rfl, show regionData 53 4 = (-29/10 : ℚ) from rfl, show regionData 53 5 = (17/12 : ℚ) from rfl] at l1 l2 l3 l4
    push_cast at l1 l2 l3 l4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · simp only [show regionData 66 0 = (211/432 : ℚ) from rfl, show regionData 66 1 = (281/570 : ℚ) from rfl, show regionData 66 2 = (-58/9 : ℚ) from rfl, show regionData 66 3 = (89/27 : ℚ) from rfl, show regionData 66 4 = (-70/11 : ℚ) from rfl, show regionData 66 5 = (36/11 : ℚ) from rfl] at l1 l2 l3 l4
    push_cast at l1 l2 l3 l4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Jia page 263 display 48 with page 280: a rough cofactor m of B_pq/pq maps to pq m in
B_pq, so the count S of B_pq and q is at least the sifted cofactor count of Lemma 21. -/
theorem roughCount_ge_sieved {Y : ℝ} {p q : ℕ} (hY : 0 < Y) (hp : p.Prime) (hq : q.Prime)
    (hqp : q < p) :
    (Sieve565.sieved (Ioc ⌊Y / ((p : ℝ) * q)⌋₊ ⌊2 * (Y / ((p : ℝ) * q))⌋₊) 1 q).card ≤
      roughCount Y (p * q) q := by
  have hd0 : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hdR : (0 : ℝ) < (p : ℝ) * q := by exact_mod_cast hd0
  unfold roughCount
  apply Finset.card_le_card_of_injOn (fun m => p * q * m)
  · intro m hm
    obtain ⟨hmI, hmS⟩ := mem_filter.mp hm
    have hlow : Y / ((p : ℝ) * q) < (m : ℝ) := Nat.lt_of_floor_lt (mem_Ioc.mp hmI).1
    have hhigh : (m : ℝ) ≤ 2 * (Y / ((p : ℝ) * q)) :=
      (Nat.cast_le.mpr (mem_Ioc.mp hmI).2).trans (Nat.floor_le (by positivity))
    have hdmL : Y < ((p * q * m : ℕ) : ℝ) := by
      rw [div_lt_iff₀ hdR] at hlow
      push_cast
      nlinarith
    have hdmU : ((p * q * m : ℕ) : ℝ) ≤ 2 * Y := by
      have h := mul_le_mul_of_nonneg_right hhigh hdR.le
      have he : 2 * (Y / ((p : ℝ) * q)) * ((p : ℝ) * q) = 2 * Y := by
        rw [mul_assoc, div_mul_cancel₀ Y hdR.ne']
      rw [he] at h
      push_cast
      nlinarith
    apply mem_filter.mpr
    refine ⟨mem_Ioc.mpr ⟨(Nat.floor_lt (by linarith)).mpr hdmL, Nat.le_floor hdmU⟩,
      dvd_mul_right _ _, ?_⟩
    · intro r hr hrz hrdm
      rcases hr.dvd_mul.mp hrdm with hrd | hrm
      · rcases hr.dvd_mul.mp hrd with hrp | hrq
        · have he : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp hrp
          subst r
          have : (q : ℝ) < p := by exact_mod_cast hqp
          linarith
        · have he : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp hrq
          subst r
          linarith
      · exact hmS r hr hrz (fun h => hr.ne_one (Nat.dvd_one.mp h)) hrm
  · intro m hm k hk hmk
    exact Nat.eq_of_mul_eq_mul_left hd0 hmk

/-- Page 280 support: the reciprocal prime sum over Y^(16/135) to Y^(1/2) is at most 18,
from three blocks of the proved lab Mertens bound Decomp588c.power_prime_sum_le_six. -/
theorem half_prime_recip_le {Y : ℝ} (hY : 1 < Y) (hlog : 28 ≤ (16 / 135 : ℝ) * Real.log Y) :
    (∑ p ∈ Decomp588b.powerPrimes Y (16 / 135) (1 / 2), (1 : ℝ) / p) ≤ 18 := by
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hsplit : Decomp588b.powerPrimes Y (16 / 135) (1 / 2) ⊆
      (Decomp588b.powerPrimes Y (16 / 135) (32 / 135) ∪
        Decomp588b.powerPrimes Y (32 / 135) (64 / 135)) ∪
        Decomp588b.powerPrimes Y (64 / 135) (1 / 2) := by
    intro p hp
    rw [Decomp588b.mem_powerPrimes hY0] at hp
    rw [mem_union, mem_union, Decomp588b.mem_powerPrimes hY0, Decomp588b.mem_powerPrimes hY0,
      Decomp588b.mem_powerPrimes hY0]
    by_cases h1 : (p : ℝ) ≤ Y ^ (32 / 135 : ℝ)
    · exact Or.inl (Or.inl ⟨hp.1, hp.2.1, h1⟩)
    · by_cases h2 : (p : ℝ) ≤ Y ^ (64 / 135 : ℝ)
      · exact Or.inl (Or.inr ⟨hp.1, not_le.mp h1, h2⟩)
      · exact Or.inr ⟨hp.1, not_le.mp h2, hp.2.2⟩
  have hl : 0 < Real.log Y := Real.log_pos hY
  have a1 := Decomp588c.power_prime_sum_le_six hY (by norm_num : (16 / 135 : ℝ) ≤ 32 / 135)
    (by norm_num) hlog
  have a2 := Decomp588c.power_prime_sum_le_six hY (by norm_num : (32 / 135 : ℝ) ≤ 64 / 135)
    (by norm_num) (by linarith)
  have a3 := Decomp588c.power_prime_sum_le_six hY (by norm_num : (64 / 135 : ℝ) ≤ 1 / 2)
    (by norm_num) (by linarith)
  have hf : ∀ x : ℕ, 0 ≤ (1 : ℝ) / x := fun x => by positivity
  have hs := sum_le_sum_of_subset_of_nonneg hsplit (f := fun p : ℕ => (1 : ℝ) / p)
    (fun x _ _ => hf x)
  have u1 := sum_union_inter (s₁ := Decomp588b.powerPrimes Y (16 / 135) (32 / 135) ∪
      Decomp588b.powerPrimes Y (32 / 135) (64 / 135))
    (s₂ := Decomp588b.powerPrimes Y (64 / 135) (1 / 2)) (f := fun p : ℕ => (1 : ℝ) / p)
  have u2 := sum_union_inter (s₁ := Decomp588b.powerPrimes Y (16 / 135) (32 / 135))
    (s₂ := Decomp588b.powerPrimes Y (32 / 135) (64 / 135)) (f := fun p : ℕ => (1 : ℝ) / p)
  have i1 : 0 ≤ ∑ x ∈ (Decomp588b.powerPrimes Y (16 / 135) (32 / 135) ∪
      Decomp588b.powerPrimes Y (32 / 135) (64 / 135)) ∩
      Decomp588b.powerPrimes Y (64 / 135) (1 / 2), (1 : ℝ) / x := sum_nonneg fun x _ => hf x
  have i2 : 0 ≤ ∑ x ∈ Decomp588b.powerPrimes Y (16 / 135) (32 / 135) ∩
      Decomp588b.powerPrimes Y (32 / 135) (64 / 135), (1 : ℝ) / x := sum_nonneg fun x _ => hf x
  linarith

/-- Jia pages 280 to 282 with Lemma 21 on page 262: for a family of source regions whose
data give Y^(16/135) < q < p, p at most Y^(1/2) and p q^2 at most Y^(9/10), the arithmetic
B model is at least the Lemma 21 main term minus eta Y / log Y.
CONDITIONAL ON Decomp578c.lemma21_rough_asymptotic, the existing LEAF for Lemma 21. -/
theorem rough_lemma21_sum_of_logs (labels : Finset ℕ)
    (hlogs : ∀ Y : ℝ, 1 < Y → ∀ p q : ℕ, p.Prime → q.Prime → regionIndex Y p q ∈ labels →
      (16 / 135) * Real.log Y < Real.log q ∧ Real.log q < Real.log p ∧
      Real.log p ≤ (1 / 2) * Real.log Y ∧
      Real.log p + 2 * Real.log q ≤ (9 / 10) * Real.log Y)
    (w : ℝ → ℝ) (hw : IsBuchstab w) (η : ℝ) (hη : 0 < η) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      buchstabMain labels w Y - η * (Y / Real.log Y) ≤ roughModel labels Y := by
  set ξ : ℝ := η / 2734 with hξdef
  have hξ : 0 < ξ := by rw [hξdef]; positivity
  obtain ⟨T, Z, hT, hZ, hcount⟩ :=
    Decomp578c.lemma21_rough_asymptotic w hw.1 hw.2.1 hw.2.2 ξ hξ
  obtain ⟨Y1, h1⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
      (Filter.eventually_ge_atTop T))
  obtain ⟨Y2, h2⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 16 / 135)).eventually
      (Filter.eventually_ge_atTop Z))
  obtain ⟨Y3, h3⟩ := Filter.eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (240 : ℝ)))
  refine ⟨max 2 (max Y1 (max Y2 Y3)), ?_⟩
  intro Y hY
  have hY2 : 2 ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 < Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hYa : Y1 ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYb : Y2 ≤ Y :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hYc : Y3 ≤ Y :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hL : 0 < Real.log Y := Real.log_pos hY1
  have hlog : 28 ≤ (16 / 135 : ℝ) * Real.log Y := by linarith [h3 Y hYc]
  set K : ℝ := ξ * ((135 / 16) * (Y / Real.log Y)) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  set P := Decomp588b.powerPrimes Y (16 / 135) (1 / 2) with hP
  have hterm : ∀ p q : ℕ,
      (if p.Prime ∧ q.Prime ∧ regionIndex Y p q ∈ labels then
        w (Real.log (Y / ((p : ℝ) * q)) / Real.log q) * ((Y / ((p : ℝ) * q)) / Real.log q)
      else 0) - K * (if p ∈ P ∧ q ∈ P then 1 / ((p : ℝ) * q) else 0) ≤
      (if p.Prime ∧ q.Prime ∧ regionIndex Y p q ∈ labels then (roughCount Y (p * q) q : ℝ)
        else 0) := by
    intro p q
    split_ifs with hc hPQ hPQ
    · obtain ⟨hp, hq, hl⟩ := hc
      obtain ⟨g1, g2, g3, g4⟩ := hlogs Y hY1 p q hp hq hl
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
      have hqpR : (q : ℝ) < p := (Real.log_lt_log_iff hq0 hp0).mp g2
      have hqp : q < p := by exact_mod_cast hqpR
      set t : ℝ := Y / ((p : ℝ) * q) with ht
      have hlt : Real.log t = Real.log Y - (Real.log p + Real.log q) := by
        rw [ht, Real.log_div hY0.ne' (by positivity), Real.log_mul hp0.ne' hq0.ne']
      have ht0 : 0 < t := by positivity
      have htT : T ≤ t := by
        refine (h1 Y hYa).trans ?_
        rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hY0 _) ht0, Real.log_rpow hY0, hlt]
        linarith
      have hqZ : Z ≤ (q : ℝ) := by
        refine (h2 Y hYb).trans ?_
        rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hY0 _) hq0, Real.log_rpow hY0]
        linarith
      have hqt : (q : ℝ) ≤ t := by
        rw [← Real.log_le_log_iff hq0 ht0, hlt]
        linarith
      have hc' := hcount t q htT hqZ hqt
      have hlow := (abs_le.mp hc').1
      have hinj := roughCount_ge_sieved hY0 hp hq hqp
      have hinjR : ((Sieve565.sieved (Ioc ⌊t⌋₊ ⌊2 * t⌋₊) 1 q).card : ℝ) ≤
          (roughCount Y (p * q) q : ℝ) := Nat.cast_le.mpr hinj
      have hlq : (16 / 135) * Real.log Y ≤ Real.log q := g1.le
      have hlq0 : 0 < Real.log q := by linarith
      have herr : ξ * (t / Real.log q) ≤ K * (1 / ((p : ℝ) * q)) := by
        rw [hK]
        have e1 : t / Real.log q ≤ (135 / 16) * (Y / Real.log Y) * (1 / ((p : ℝ) * q)) := by
          rw [ht, div_div, show (135 / 16) * (Y / Real.log Y) * (1 / ((p : ℝ) * q)) =
            Y / ((p : ℝ) * q * ((16 / 135) * Real.log Y)) by field_simp]
          apply div_le_div_of_nonneg_left hY0.le (by positivity)
          exact mul_le_mul_of_nonneg_left hlq (by positivity)
        have := mul_le_mul_of_nonneg_left e1 hξ.le
        linarith
      linarith
    · exfalso
      obtain ⟨hp, hq, hl⟩ := hc
      obtain ⟨g1, g2, g3, -⟩ := hlogs Y hY1 p q hp hq hl
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
      apply hPQ
      rw [hP, Decomp588b.mem_powerPrimes hY0.le, Decomp588b.mem_powerPrimes hY0.le]
      refine ⟨⟨hp, ?_, ?_⟩, ⟨hq, ?_, ?_⟩⟩
      · rw [← Real.log_lt_log_iff (Real.rpow_pos_of_pos hY0 _) hp0, Real.log_rpow hY0]
        linarith
      · rw [← Real.log_le_log_iff hp0 (Real.rpow_pos_of_pos hY0 _), Real.log_rpow hY0]
        linarith
      · rw [← Real.log_lt_log_iff (Real.rpow_pos_of_pos hY0 _) hq0, Real.log_rpow hY0]
        linarith
      · rw [← Real.log_le_log_iff hq0 (Real.rpow_pos_of_pos hY0 _), Real.log_rpow hY0]
        linarith
    · have : 0 ≤ 1 / ((p : ℝ) * q) := by positivity
      nlinarith
    · simp
  have hsum := sum_le_sum fun p (_ : p ∈ range (⌊2 * Y⌋₊ + 1)) =>
    sum_le_sum fun q (_ : q ∈ range (⌊2 * Y⌋₊ + 1)) => hterm p q
  simp only [sum_sub_distrib, ← mul_sum] at hsum
  have hrec : ∑ p ∈ range (⌊2 * Y⌋₊ + 1), ∑ q ∈ range (⌊2 * Y⌋₊ + 1),
      (if p ∈ P ∧ q ∈ P then 1 / ((p : ℝ) * q) else 0) ≤ 18 * 18 := by
    have hPs := half_prime_recip_le hY1 hlog
    have hP0 : 0 ≤ ∑ p ∈ P, (1 : ℝ) / p := sum_nonneg fun _ _ => by positivity
    calc _ = ∑ x ∈ range (⌊2 * Y⌋₊ + 1) ×ˢ range (⌊2 * Y⌋₊ + 1),
          (if x.1 ∈ P ∧ x.2 ∈ P then 1 / ((x.1 : ℝ) * x.2) else 0) := by
          rw [sum_product]
      _ ≤ ∑ x ∈ P ×ˢ P, (if x.1 ∈ P ∧ x.2 ∈ P then 1 / ((x.1 : ℝ) * x.2) else 0) := by
          rw [← sum_filter_ne_zero]
          apply sum_le_sum_of_subset_of_nonneg
          · intro x hx
            obtain ⟨-, hx⟩ := mem_filter.mp hx
            split_ifs at hx with hc
            · exact mem_product.mpr hc
            · exact absurd rfl hx
          · intro x _ _; split_ifs <;> positivity
      _ = ∑ x ∈ P ×ˢ P, 1 / ((x.1 : ℝ) * x.2) := by
          apply sum_congr rfl
          intro x hx
          rw [if_pos (mem_product.mp hx)]
      _ = (∑ p ∈ P, (1 : ℝ) / p) * (∑ p ∈ P, (1 : ℝ) / p) := by
          rw [sum_product, sum_mul_sum]
          simp only [one_div_mul_one_div]
      _ ≤ 18 * 18 := mul_le_mul hPs hPs hP0 (by norm_num)
  have hKb : K * (18 * 18) ≤ η * (Y / Real.log Y) := by
    rw [hK, hξdef]
    have : 0 ≤ Y / Real.log Y := by positivity
    nlinarith
  unfold buchstabMain roughModel
  have := mul_le_mul_of_nonneg_left hrec hK0
  linarith

/-- REDUCED, formerly LEAF: Jia pages 280 and 281 with Lemma 21 on page 262, applied to each cofactor count
S of B_pq and q over regions 33, 36, 38, 40, 42, 46 and 49, then summed; the Lemma 21 error
is absorbed by the Mertens bound for the sum of t over log q over these regions. HARD
CONDITIONAL ON Decomp578c.lemma21_rough_asymptotic, the Lemma 21 LEAF already on main;
no new sorry, S140. -/
theorem rough11_lemma21_sum (w : ℝ → ℝ) (hw : IsBuchstab w) (η : ℝ) (hη : 0 < η) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      buchstabMain labels11 w Y - η * (Y / Real.log Y) ≤ roughModel labels11 Y :=
  rough_lemma21_sum_of_logs labels11 labels11_logs w hw η hη

/-- LEAF: Jia pages 280 and 281, the prime number theorem Riemann sum step: the double prime
sum of the Lemma 21 main term over regions 33, 36, 38, 40, 42, 46 and 49 is at least the
Buchstab integral over the nine printed subdomains, rows two to ten, times Y over log Y. HARD -/
theorem buchstabMain11_riemann (w : ℝ → ℝ) (hw : IsBuchstab w) (η : ℝ) (hη : 0 < η) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ((∑ i ∈ (Finset.univ.filter (fun i : Fin 16 => i.val < 9)), fullRow w i) - η) *
        (Y / Real.log Y) ≤ buchstabMain labels11 w Y := by sorry

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
#print axioms labels11_logs
#print axioms labels12_logs
#print axioms roughCount_ge_sieved
#print axioms half_prime_recip_le
#print axioms rough_lemma21_sum_of_logs
#print axioms rough11_lemma21_sum
#print axioms buchstabMain11_riemann
#print axioms family_from_buchstab
#print axioms rough11_to_integral_from_leaves
end
end LeanLab.Languasco2004.Feed564bRough

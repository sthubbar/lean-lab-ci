/-
Jia 1996 pages 280 to 282 with display 40 on page 261.
Source https://doi.org/10.4064/aa-77-3-207-287.
Split of Feed564bRough.buchstabMain11_riemann and Feed564cRough.buchstabMain12_riemann,
burst-20261122, session S140. Each splits into a region inclusion step, the printed
subdomains of pages 281 and 282 lie in the Lemma 11 or Lemma 12 source regions, and a PNT
Riemann sum step on the printed subdomains.
The assemblies below have the exact parent types; the parents stay open leaves because
this module must import Feed564bRough, so the wiring is left to a later merge.
Analytic leaves stay OPEN. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Feed564bRowData12

namespace LeanLab.Languasco2004.Feed564bRiemann
open Finset Real Decomp279a Decomp316c Model564 RemainderData564 Feed564bRough
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Pages 280 to 282: the Lemma 21 main term of buchstabMain summed only over prime pairs
in the union of a family of printed subdomains. -/
def rowPairSum (rows : Finset (Fin 16)) (w : ℝ → ℝ) (Y : ℝ) : ℝ :=
  ∑ p ∈ range (⌊2 * Y⌋₊ + 1), ∑ q ∈ range (⌊2 * Y⌋₊ + 1),
    if p.Prime ∧ q.Prime ∧ ∃ i ∈ rows, rowMem i Y p q then
      w (Real.log (Y / ((p : ℝ) * q)) / Real.log q) * ((Y / ((p : ℝ) * q)) / Real.log q)
    else 0

/-- PROVED, formerly LEAF: Jia pages 267 to 269 and 281: every prime pair in printed subdomains two to ten has
its first matching region among 33, 36, 38, 40, 42, 46, 49, and the Buchstab function is
nonnegative from 1 on, so the row sum is at most buchstabMain over labels11. Checked
numerically on 180000 interior sample points, all in those regions. MEDIUM -/
theorem rowPairSum11_le_buchstabMain (w : ℝ → ℝ) (hw : IsBuchstab w) (Y : ℝ) (hY : 2 ≤ Y) :
    rowPairSum (Finset.univ.filter (fun i : Fin 16 => i.val < 9)) w Y ≤
      buchstabMain labels11 w Y := by
  have hY1 : 1 < Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hL : 0 < Real.log Y := Real.log_pos hY1
  unfold rowPairSum buchstabMain
  apply sum_le_sum
  intro p _
  apply sum_le_sum
  intro q _
  by_cases hrow : p.Prime ∧ q.Prime ∧
      ∃ i ∈ Finset.univ.filter (fun i : Fin 16 => i.val < 9), rowMem i Y p q
  · obtain ⟨hp, hq, i, hi, hm⟩ := hrow
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hlab : regionIndex Y p q ∈ labels11 := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have key : ∀ j : Fin 16, j.val < 9 →
          j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by decide
      rcases key i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact row0_region11 Y hY1 p q hp0 hq0 hm
      · exact row1_region11 Y hY1 p q hp0 hq0 hm
      · exact row2_region11 Y hY1 p q hp0 hq0 hm
      · exact row3_region11 Y hY1 p q hp0 hq0 hm
      · exact row4_region11 Y hY1 p q hp0 hq0 hm
      · exact row5_region11 Y hY1 p q hp0 hq0 hm
      · exact row6_region11 Y hY1 p q hp0 hq0 hm
      · exact row7_region11 Y hY1 p q hp0 hq0 hm
      · exact row8_region11 Y hY1 p q hp0 hq0 hm
    rw [if_pos ⟨hp, hq, i, hi, hm⟩, if_pos ⟨hp, hq, hlab⟩]
  · rw [if_neg hrow]
    split_ifs with hc
    · obtain ⟨hp, hq, hl⟩ := hc
      obtain ⟨g1, g2, g3, g4⟩ := labels11_logs Y hY1 p q hp hq hl
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
      have hlq : 0 < Real.log q := by linarith
      have harg : 1 ≤ Real.log (Y / ((p : ℝ) * q)) / Real.log q := by
        rw [le_div_iff₀ hlq, Real.log_div hY0.ne' (by positivity), Real.log_mul hp0.ne' hq0.ne']
        linarith
      have h1 := isBuchstab_nonneg w hw _ harg
      have h2 : 0 ≤ (Y / ((p : ℝ) * q)) / Real.log q := by positivity
      exact mul_nonneg h1 h2
    · exact le_rfl


/-- LEAF: Jia pages 280 and 281: Mertens and the prime number theorem Riemann sum over
p = Y^t and q = Y^u turn the row sum into Y / log Y times the Buchstab integral of
w((1-t-u)/u)/(t u^2) over printed subdomains two to ten, up to any fixed loss. HARD -/
theorem rowPairSum11_riemann (w : ℝ → ℝ) (hw : IsBuchstab w) (η : ℝ) (hη : 0 < η) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ((∑ i ∈ (Finset.univ.filter (fun i : Fin 16 => i.val < 9)), fullRow w i) - η) *
        (Y / Real.log Y) ≤ rowPairSum (Finset.univ.filter (fun i : Fin 16 => i.val < 9)) w Y := by
  sorry

/-- PROVED, formerly LEAF: Jia pages 267 to 269 and 282: every prime pair in printed subdomains eleven to
seventeen has its first matching region among 53 and 66, and the Buchstab function is
nonnegative from 1 on. Checked numerically on 140000 interior sample points. MEDIUM -/
theorem rowPairSum12_le_buchstabMain (w : ℝ → ℝ) (hw : IsBuchstab w) (Y : ℝ) (hY : 2 ≤ Y) :
    rowPairSum (Finset.univ.filter (fun i : Fin 16 => ¬ i.val < 9)) w Y ≤
      buchstabMain labels12 w Y := by
  have hY1 : 1 < Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hL : 0 < Real.log Y := Real.log_pos hY1
  unfold rowPairSum buchstabMain
  apply sum_le_sum
  intro p _
  apply sum_le_sum
  intro q _
  by_cases hrow : p.Prime ∧ q.Prime ∧
      ∃ i ∈ Finset.univ.filter (fun i : Fin 16 => ¬ i.val < 9), rowMem i Y p q
  · obtain ⟨hp, hq, i, hi, hm⟩ := hrow
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hlab : regionIndex Y p q ∈ labels12 := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have key : ∀ j : Fin 16, ¬ j.val < 9 →
          j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by decide
      rcases key i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [row9_region Y hY1 p q hp0 hq0 hm]; decide
      · rw [row10_region Y hY1 p q hp0 hq0 hm]; decide
      · rw [row11_region Y hY1 p q hp0 hq0 hm]; decide
      · rw [row12_region Y hY1 p q hp0 hq0 hm]; decide
      · rw [row13_region Y hY1 p q hp0 hq0 hm]; decide
      · rw [row14_region Y hY1 p q hp0 hq0 hm]; decide
      · rw [row15_region Y hY1 p q hp0 hq0 hm]; decide
    rw [if_pos ⟨hp, hq, i, hi, hm⟩, if_pos ⟨hp, hq, hlab⟩]
  · rw [if_neg hrow]
    split_ifs with hc
    · obtain ⟨hp, hq, hl⟩ := hc
      obtain ⟨g1, g2, g3, g4⟩ := labels12_logs Y hY1 p q hp hq hl
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
      have hlq : 0 < Real.log q := by linarith
      have harg : 1 ≤ Real.log (Y / ((p : ℝ) * q)) / Real.log q := by
        rw [le_div_iff₀ hlq, Real.log_div hY0.ne' (by positivity), Real.log_mul hp0.ne' hq0.ne']
        linarith
      have h1 := isBuchstab_nonneg w hw _ harg
      have h2 : 0 ≤ (Y / ((p : ℝ) * q)) / Real.log q := by positivity
      exact mul_nonneg h1 h2
    · exact le_rfl


/-- LEAF: Jia pages 281 and 282: the Riemann sum step on printed subdomains eleven to
seventeen. HARD -/
theorem rowPairSum12_riemann (w : ℝ → ℝ) (hw : IsBuchstab w) (η : ℝ) (hη : 0 < η) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ((∑ i ∈ (Finset.univ.filter (fun i : Fin 16 => ¬ i.val < 9)), fullRow w i) - η) *
        (Y / Real.log Y) ≤ rowPairSum (Finset.univ.filter (fun i : Fin 16 => ¬ i.val < 9)) w Y := by
  sorry

/-- Jia pages 280 and 281: exact type of Feed564bRough.buchstabMain11_riemann.
CONDITIONAL ON rowPairSum11_le_buchstabMain and rowPairSum11_riemann. -/
theorem buchstabMain11_riemann_from_leaves (w : ℝ → ℝ) (hw : IsBuchstab w) (η : ℝ) (hη : 0 < η) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ((∑ i ∈ (Finset.univ.filter (fun i : Fin 16 => i.val < 9)), fullRow w i) - η) *
        (Y / Real.log Y) ≤ buchstabMain labels11 w Y := by
  obtain ⟨Y₀, h⟩ := rowPairSum11_riemann w hw η hη
  exact ⟨max Y₀ 2, fun Y hY => (h Y ((le_max_left _ _).trans hY)).trans
    (rowPairSum11_le_buchstabMain w hw Y ((le_max_right _ _).trans hY))⟩

/-- Jia pages 281 and 282: exact type of Feed564cRough.buchstabMain12_riemann.
CONDITIONAL ON rowPairSum12_le_buchstabMain and rowPairSum12_riemann. -/
theorem buchstabMain12_riemann_from_leaves (w : ℝ → ℝ) (hw : IsBuchstab w) (η : ℝ) (hη : 0 < η) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ((∑ i ∈ (Finset.univ.filter (fun i : Fin 16 => ¬ i.val < 9)), fullRow w i) - η) *
        (Y / Real.log Y) ≤ buchstabMain labels12 w Y := by
  obtain ⟨Y₀, h⟩ := rowPairSum12_riemann w hw η hη
  exact ⟨max Y₀ 2, fun Y hY => (h Y ((le_max_left _ _).trans hY)).trans
    (rowPairSum12_le_buchstabMain w hw Y ((le_max_right _ _).trans hY))⟩

#print axioms rowPairSum
#print axioms rowPairSum11_le_buchstabMain
#print axioms rowPairSum11_riemann
#print axioms rowPairSum12_le_buchstabMain
#print axioms rowPairSum12_riemann
#print axioms buchstabMain11_riemann_from_leaves
#print axioms buchstabMain12_riemann_from_leaves
end
end LeanLab.Languasco2004.Feed564bRiemann

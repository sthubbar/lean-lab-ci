import LeanLab.Routes.U1554LinnikGRH

namespace LeanLab.Routes.U1554LinnikGRH

private theorem carryCoeffs191_getD (num : ℕ) (j : Fin 16) :
    (carryCoeffs191 num)[j.val]?.getD 0 =
      num ^ j.val * 20000 ^ (15 - j.val) *
        (Nat.factorial 15 / Nat.factorial j.val) := by
  simp [carryCoeffs191, Array.getElem?_ofFn]

private theorem carryWeights191_getD (num : ℕ) (t : Fin 31) :
    (carryWeights191 num)[t.val]?.getD 0 =
      ∑ j ∈ Finset.range 16,
        if t.val ≤ j + 15 ∧ j ≤ t.val then
          (carryCoeffs191 num)[j]?.getD 0 *
            (carryCoeffs191 num)[j + 15 - t.val]?.getD 0 else 0 := by
  simp [carryWeights191, Array.getElem?_ofFn]

private theorem carryStep191_getD (w v : Array ℕ) (j : Fin 31) :
    (carryStep191 w v)[j.val]?.getD 0 =
      ∑ i ∈ Finset.range 31,
        if i ≤ 2 * j.val ∧ 2 * j.val ≤ i + 30 then
          v[i]?.getD 0 * w[2 * j.val - i]?.getD 0 else 0 := by
  simp [carryStep191, Array.getElem?_ofFn]

private theorem carryRows191_getD (w : Array ℕ) (h : ℕ) (j : Fin 31) :
    (carryRows191 w h)[j.val]?.getD 0 =
      if h = 0 then if j.val = 15 then 1 else 0 else
        ∑ i ∈ Finset.range 31,
          if i ≤ 2 * j.val ∧ 2 * j.val ≤ i + 30 then
            (carryRows191 w h)[i]?.getD 0 * w[2 * j.val - i]?.getD 0 else 0 := by
  induction h with
  | zero => simp [carryRows191, Array.getElem?_ofFn]
  | succ h ih =>
    simp only [carryRows191]
    rw [carryStep191_getD]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hc : i ≤ 2 * j.val ∧ 2 * j.val ≤ i + 30
    · simp only [hc, ↓reduceIte]
      rw [ih]
    · simp [hc]

end LeanLab.Routes.U1554LinnikGRH

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

example (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 6 + 6*y ^ 5 + 30*y ^ 4 + 120*y ^ 3 + 360*y ^ 2 + 720*y + 720)
      (720*x ^ 5 + 1800*x ^ 4 + 3600*x ^ 3 + 3600*x ^ 2 + 1440*x + 720) x := by
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := by
    simpa only [id] using (hasDerivAt_id (𝕜 := ℝ) x)
  have h1 := hid.pow 6
  have h2 := HasDerivAt.const_mul 6 (hid.pow 5)
  have h3 := HasDerivAt.const_mul 30 (hid.pow 4)
  have h4 := HasDerivAt.const_mul 120 (hid.pow 3)
  have h5 := HasDerivAt.const_mul 360 (hid.pow 2)
  have h6 := HasDerivAt.const_mul 720 hid
  have h7 := hasDerivAt_const x (720:ℝ)
  have hs := h1.add h2
  have hs2 := hs.add h3
  have hs3 := hs2.add h4
  have hs4 := hs3.add h5
  have hs5 := hs4.add h6
  have hs6 := hs5.add h7
  convert hs6 using 1 <;> ring

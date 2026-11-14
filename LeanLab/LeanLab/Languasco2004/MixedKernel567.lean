/-
Jia 1996 pages 275 to 277, compact logarithmic minorants for Lemma 25.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.RealCertificate567
import LeanLab.Languasco2004.Numeric30_548

namespace LeanLab.Languasco2004.MixedKernel567
open Real Polynomial567 Numeric548 Numeric30_548
noncomputable section

/-- Pages 275 to 277 numerical support: two centered geometric reciprocal terms. -/
def invPoly1 (x c : ℝ) : ℝ := (2-x/c)/c

/-- Pages 275 to 277: even length reciprocal enclosures increase with their length. -/
theorem short_reciprocal_chain (x c : ℝ) (hx : 0 < x) (hc : 0 < c)
    (hxc : x ≤ 2*c) :
    0 ≤ invPoly1 x c ∧ invPoly1 x c ≤ invPoly3 x c ∧ invPoly3 x c ≤ invPoly5 x c := by
  have hz : 0 ≤ 2-x/c := by
    have := (div_le_iff₀ hc).mpr hxc
    linarith
  have h1 : 0 ≤ invPoly1 x c := by unfold invPoly1; positivity
  have he13 : invPoly3 x c - invPoly1 x c = (1-x/c)^2*(2-x/c)/c := by
    unfold invPoly3 invPoly1
    ring
  have he35 : invPoly5 x c - invPoly3 x c = (1-x/c)^4*(2-x/c)/c := by
    unfold invPoly5 invPoly3
    ring
  have hp13 : 0 ≤ (1-x/c)^2*(2-x/c)/c := by positivity
  have hp35 : 0 ≤ (1-x/c)^4*(2-x/c)/c := by positivity
  exact ⟨h1, by linarith, by linarith⟩

/-- Pages 275 to 277: use shorter reciprocal polynomials in the smaller odd series terms. -/
def mixedMinorant (ct cu cv t u : ℝ) : ℝ :=
  let pt := invPoly5 t ct
  let pu := invPoly7 u cu
  let v5 := invPoly5 (1-t-u) cv
  let v3 := invPoly3 (1-t-u) cv
  let v1 := invPoly1 (1-t-u) cv
  let w := 1-t-3*u
  pt*pu*(v5+2*w*v5^2+(2/3)*w^3*v3^4+(2/5)*w^5*v1^6+(2/7)*w^7*v1^8)

/-- Pages 275 to 277: the compact polynomial is below the existing full polynomial.
All printed integral targets are therefore preserved. -/
theorem mixed_le_full (ct cu cv t u : ℝ)
    (ht : 0 < t) (hu : 0 < u) (hv : 0 < 1-t-u) (hw : 0 ≤ 1-t-3*u)
    (hct : 0 < ct) (hcu : 0 < cu) (hcv : 0 < cv)
    (hT : t ≤ 2*ct) (hU : u ≤ 2*cu) (hV : 1-t-u ≤ 2*cv) :
    mixedMinorant ct cu cv t u ≤ minorant 1 ct cu cv t u := by
  obtain ⟨ht0, ht1⟩ := invPoly5_centered t ct ht hct hT
  obtain ⟨hu0, hu1⟩ := invPoly7_centered u cu hu hcu hU
  obtain ⟨hv10, hv13, hv35⟩ := short_reciprocal_chain (1-t-u) cv hv hcv hV
  have hv30 : 0 ≤ invPoly3 (1-t-u) cv := hv10.trans hv13
  have hv15 := hv13.trans hv35
  have h4 := pow_le_pow_left₀ hv30 hv35 4
  have h6 := pow_le_pow_left₀ hv10 hv15 6
  have h8 := pow_le_pow_left₀ hv10 hv15 8
  have h3 := mul_le_mul_of_nonneg_left h4
    (show (0 : ℝ) ≤ (2/3)*(1-t-3*u)^3 by positivity)
  have h5 := mul_le_mul_of_nonneg_left h6
    (show (0 : ℝ) ≤ (2/5)*(1-t-3*u)^5 by positivity)
  have h7 := mul_le_mul_of_nonneg_left h8
    (show (0 : ℝ) ≤ (2/7)*(1-t-3*u)^7 by positivity)
  have hs := add_le_add (add_le_add (add_le_add_left h3
    (invPoly5 (1-t-u) cv + 2*(1-t-3*u)*invPoly5 (1-t-u) cv^2)) h5) h7
  have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg ht0 hu0)
  calc
    mixedMinorant ct cu cv t u ≤
        invPoly5 t ct*invPoly7 u cu*(invPoly5 (1-t-u) cv+
          2*(1-t-3*u)*invPoly5 (1-t-u) cv^2+
          (2/3)*(1-t-3*u)^3*invPoly5 (1-t-u) cv^4+
          (2/5)*(1-t-3*u)^5*invPoly5 (1-t-u) cv^6+
          (2/7)*(1-t-3*u)^7*invPoly5 (1-t-u) cv^8) := by
      convert hm using 1 <;> (try dsimp [mixedMinorant]) <;> ring
    _ = minorant 1 ct cu cv t u := by simp [minorant]; ring

#print axioms short_reciprocal_chain
#print axioms mixed_le_full
end
end LeanLab.Languasco2004.MixedKernel567

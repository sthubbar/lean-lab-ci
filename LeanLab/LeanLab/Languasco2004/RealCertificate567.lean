/-
Jia 1996 pages 275 to 277, exact polynomial certificates for Lemma 25.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.PolynomialCertificate567

namespace LeanLab.Languasco2004.RealCertificate567
open Polynomial Real intervalIntegral PolynomialCertificate567
noncomputable section

/-- Pages 275 to 277 numerical support: evaluate a real polynomial in the reals. -/
def evalR (p : Polynomial ℝ) (x : ℝ) : ℝ := p.eval₂ (RingHom.id ℝ) x

/-- Pages 275 to 277 numerical support: evaluate a polynomial in t and u. -/
def evalRR (p : Polynomial (Polynomial ℝ)) (t u : ℝ) : ℝ :=
  p.eval₂ (Polynomial.eval₂RingHom (RingHom.id ℝ) t) u

/-- Pages 275 to 277: pointwise derivative evaluations suffice for an exact certificate.
The polynomial primitives supply every integrability premise. -/
theorem real_integral_evaluation_certificate (F : ℝ → ℝ → ℝ)
    (q : Polynomial (Polynomial ℝ)) (L U s : Polynomial ℝ)
    (hinner : ∀ t u : ℝ, evalRR q.derivative t u = F t u)
    (houter : ∀ t : ℝ, evalR s.derivative t =
      evalRR q t (evalR U t) - evalRR q t (evalR L t)) (a b : ℝ) :
    (∫ t in a..b, ∫ u in evalR L t..evalR U t, F t u) =
      evalR s b - evalR s a := by
  have hi (t : ℝ) : (∫ u in evalR L t..evalR U t, F t u) =
      evalRR q t (evalR U t) - evalRR q t (evalR L t) := by
    have he : F t = fun u => evalRR q.derivative t u :=
      funext (fun u => (hinner t u).symm)
    rw [he]
    exact integral_polynomial (Polynomial.eval₂RingHom (RingHom.id ℝ) t)
      q.derivative q rfl _ _
  calc
    _ = ∫ t in a..b, evalR s.derivative t := by
      apply integral_congr
      intro t ht
      change (∫ u in evalR L t..evalR U t, F t u) = evalR s.derivative t
      rw [hi t]
      exact (houter t).symm
    _ = _ := integral_polynomial (RingHom.id ℝ) s.derivative s rfl a b

#print axioms real_integral_evaluation_certificate
end
end LeanLab.Languasco2004.RealCertificate567

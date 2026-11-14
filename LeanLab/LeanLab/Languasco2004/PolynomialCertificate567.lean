/-
Jia 1996 pages 275 to 277, exact polynomial certificates for Lemma 25.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Polynomial567

namespace LeanLab.Languasco2004.PolynomialCertificate567
open Polynomial Real intervalIntegral Polynomial567 Numeric548
noncomputable section

/-- Pages 275 to 277 numerical support: evaluate a rational polynomial in the reals. -/
def evalQ (p : Polynomial ℚ) (x : ℝ) : ℝ := p.eval₂ (Rat.castHom ℝ) x

/-- Pages 275 to 277 numerical support: evaluate a polynomial in t and u. -/
def evalQQ (p : Polynomial (Polynomial ℚ)) (t u : ℝ) : ℝ :=
  p.eval₂ (Polynomial.eval₂RingHom (Rat.castHom ℝ) t) u

/-- Pages 275 to 277: an algebraic antiderivative identity evaluates a real integral. -/
theorem integral_polynomial {R : Type*} [CommRing R] (f : R →+* ℝ)
    (p q : Polynomial R) (h : q.derivative = p) (a b : ℝ) :
    (∫ x in a..b, p.eval₂ f x) = q.eval₂ f b - q.eval₂ f a := by
  simp only [Polynomial.eval₂_eq_eval_map]
  have hd : (q.map f).derivative = p.map f := by rw [Polynomial.derivative_map, h]
  exact integral_eq_sub_of_hasDerivAt
    (fun x _ => by simpa only [hd] using (q.map f).hasDerivAt x)
    ((p.map f).continuous.intervalIntegrable _ _)

/-- Pages 275 to 277: two rational derivative identities certify the complete iterated integral. -/
theorem integral_certificate (p q : Polynomial (Polynomial ℚ))
    (L U s : Polynomial ℚ) (hinner : q.derivative = p)
    (houter : s.derivative = q.eval U - q.eval L) (a b : ℝ) :
    (∫ t in a..b, ∫ u in evalQ L t..evalQ U t, evalQQ p t u) =
      evalQ s b - evalQ s a := by
  have hi (t : ℝ) : (∫ u in evalQ L t..evalQ U t, evalQQ p t u) =
      evalQ (q.eval U - q.eval L) t := by
    let f := Polynomial.eval₂RingHom (Rat.castHom ℝ) t
    change (∫ u in f L..f U, p.eval₂ f u) = f (q.eval U - q.eval L)
    rw [integral_polynomial f p q hinner]
    rw [Polynomial.eval₂_at_apply, Polynomial.eval₂_at_apply, map_sub]
  calc
    _ = ∫ t in a..b, evalQ (q.eval U - q.eval L) t := by
      apply integral_congr
      intro t ht
      exact hi t
    _ = _ := integral_polynomial (Rat.castHom ℝ) _ s houter a b

/-- Pages 275 to 277: pointwise derivative evaluations suffice for an exact certificate.
The polynomial primitives supply every integrability premise. -/
theorem integral_evaluation_certificate (F : ℝ → ℝ → ℝ)
    (q : Polynomial (Polynomial ℚ)) (L U s : Polynomial ℚ)
    (hinner : ∀ t u : ℝ, evalQQ q.derivative t u = F t u)
    (houter : ∀ t : ℝ, evalQ s.derivative t =
      evalQQ q t (evalQ U t) - evalQQ q t (evalQ L t)) (a b : ℝ) :
    (∫ t in a..b, ∫ u in evalQ L t..evalQ U t, F t u) =
      evalQ s b - evalQ s a := by
  have hi (t : ℝ) : (∫ u in evalQ L t..evalQ U t, F t u) =
      evalQQ q t (evalQ U t) - evalQQ q t (evalQ L t) := by
    have he : F t = fun u => evalQQ q.derivative t u :=
      funext (fun u => (hinner t u).symm)
    rw [he]
    exact integral_polynomial (Polynomial.eval₂RingHom (Rat.castHom ℝ) t)
      q.derivative q rfl _ _
  calc
    _ = ∫ t in a..b, evalQ s.derivative t := by
      apply integral_congr
      intro t ht
      change (∫ u in evalQ L t..evalQ U t, F t u) = evalQ s.derivative t
      rw [hi t]
      exact (houter t).symm
    _ = _ := integral_polynomial (Rat.castHom ℝ) s.derivative s rfl a b

#print axioms integral_polynomial
#print axioms integral_certificate
#print axioms integral_evaluation_certificate
end
end LeanLab.Languasco2004.PolynomialCertificate567

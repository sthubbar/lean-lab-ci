/-
Jia 1996 pages 271 to 273, the 25 numerical components of Lemma 24.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The constant kernel is a lower model using Lemma 20, not a definition of Buchstab's function.
-/
import LeanLab.Languasco2004.Kernel11_566

namespace LeanLab.Languasco2004.RemainderData566
open Real intervalIntegral
noncomputable section

/-- Pages 271 to 273: endpoints, affine inner bounds and kernel tags in printed order.
Tag zero is rational, one is logarithmic and two is the constant lower kernel. -/
def data : Fin 25 → Fin 7 → ℚ :=
  ![![17/57, 17/54, -12/11, 17/33, -1/3, 1/3, 1],
    ![17/57, 17/54, -1/3, 1/3, -1/8, 7/24, 0],
    ![17/54, 221/693, 0, 17/99, -1/3, 1/3, 1],
    ![17/54, 221/693, -1/3, 1/3, -1/8, 7/24, 0],
    ![221/693, 109/330, 0, 17/99, -1/3, 1/3, 1],
    ![221/693, 109/330, -1/3, 1/3, -1, 113/198, 0],
    ![109/330, 1/3, 0, 17/99, -1/3, 1/3, 1],
    ![109/330, 1/3, -1/3, 1/3, -6, 20/9, 0],
    ![1/3, 151/450, 0, 17/99, -6, 20/9, 1],
    ![151/450, 34/99, 0, 17/99, 1/4, 1/8, 1],
    ![151/450, 34/99, -1, 5/9, -1/3, 1/3, 1],
    ![151/450, 34/99, -1/3, 1/3, 1/3, 7/54, 0],
    ![34/99, 25/72, -58/49, 85/147, 1/4, 1/8, 1],
    ![25/72, 193/549, -58/49, 85/147, -1/3, 1/3, 1],
    ![25/72, 193/549, -1/3, 1/3, -23/15, 7/9, 0],
    ![193/549, 10/27, -58/49, 85/147, -1/4, 1/4, 2],
    ![193/549, 10/27, -1/4, 1/4, -1/3, 1/3, 1],
    ![193/549, 10/27, -1/3, 1/3, -23/15, 7/9, 0],
    ![10/27, 617/1620, -58/49, 85/147, -1/4, 1/4, 2],
    ![10/27, 617/1620, -1/4, 1/4, -1, 47/81, 1],
    ![617/1620, 3041/7830, -58/49, 85/147, -1/4, 1/4, 2],
    ![617/1620, 3041/7830, -1/4, 1/4, -29/19, 89/114, 1],
    ![3041/7830, 121/291, 0, 16/135, -1/4, 1/4, 2],
    ![3041/7830, 121/291, -1/4, 1/4, -29/19, 89/114, 1],
    ![121/291, 3397/7830, 0, 16/135, -29/19, 89/114, 2]]

/-- Page 273: the 25 printed coefficients in source order. -/
def coefficient : Fin 25 → ℚ := ![0.035949, 0.010981, 0.010207, 0.002956, 0.026780, 0.007110, 0.006712, 0.000780, 0.004363, 0.013697, 0.001020, 0.005290, 0.007124, 0.009992, 0.003228, 0.010892, 0.045105, 0.006377, 0.016938, 0.023556, 0.017909, 0.014602, 0.066888, 0.026127, 0.020382]

/-- Pages 271 to 273 support: the lowest affine lower endpoint. -/
def uMin (i : Fin 25) : ℚ := min (data i 2 * data i 0 + data i 3)
  (data i 2 * data i 1 + data i 3)

/-- Pages 271 to 273 support: the highest affine upper endpoint. -/
def uMax (i : Fin 25) : ℚ := max (data i 4 * data i 0 + data i 5)
  (data i 4 * data i 1 + data i 5)

/-- Pages 271 to 273: the exact lower kernel selected by a source term. -/
def kernel (i : Fin 25) (t u : ℝ) : ℝ :=
  if data i 6 = 2 then 0.5607 / (t * u ^ 2)
  else if data i 6 = 1 then
    (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u))
  else 1 / (t * u * (1 - t - u))

/-- Pages 271 to 273: each explicit double integral with its exact affine bounds. -/
def term (i : Fin 25) : ℝ :=
  ∫ t in (data i 0 : ℝ)..(data i 1 : ℝ),
    ∫ u in ((data i 2 : ℝ) * t + data i 3)..((data i 4 : ℝ) * t + data i 5), kernel i t u

/-- Page 273: the lower numerical model for the 18 region remainder. -/
def model : ℝ := ∑ i : Fin 25, term i

/-- Page 273: the 25 printed components sum to the sealed remainder coefficient. -/
theorem coefficient_sum : (∑ i : Fin 25, coefficient i) = (0.394965 : ℚ) := by
  norm_num [coefficient, Fin.sum_univ_succ]

/-- Pages 271 to 273: every source term has a positive outer interval and an inner interval.
The two endpoint checks certify the affine inner width everywhere by interpolation. -/
theorem domain_certificate : ∀ i : Fin 25,
    let r := data i
    0 < r 0 ∧ r 0 < r 1 ∧
      0 < r 2 * r 0 + r 3 ∧ 0 < r 2 * r 1 + r 3 ∧
      r 2 * r 0 + r 3 ≤ r 4 * r 0 + r 5 ∧
      r 2 * r 1 + r 3 ≤ r 4 * r 1 + r 5 := by
  decide +kernel

#print axioms coefficient_sum
#print axioms domain_certificate
end
end LeanLab.Languasco2004.RemainderData566

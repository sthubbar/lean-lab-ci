import LeanLab.GoldbachAverage.TailCount402
import LeanLab.GoldbachAverage.PairKernel402
import LeanLab.GoldbachAverage.Decomp287d

/-!
BHMS, arXiv 1704.06103v2 pages 18 and 19, high zero part of Lemma 7.
The symmetry step leaves an asymmetric reciprocal square tail times a separation kernel.
Its count is proved from the ported tail and the new reciprocal kernel.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp402f
open Finset MeasureTheory
open LeanLab.PNTPort.Selberg
open Decomp287d

/-- The asymmetric high zero kernel in BHMS page 19 after the symmetry step.
The second range is enlarged to all ordinates of absolute value at most x. -/
def highPairWeight (x h : ℝ) : ℝ :=
  ∑' ρ : NontrivialZero,
    if x / h < |ρ.1.im| ∧ |ρ.1.im| ≤ x then
      ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / |ρ.1.im| ^ 2) *
        ∑' σ : NontrivialZero, if |σ.1.im| ≤ x then
          (analyticOrderNatAt riemannZeta σ.1 : ℝ) / (1 + |ρ.1.im - σ.1.im|)
        else 0
    else 0

/-- The asymmetric high pair kernel is nonnegative, BHMS page 19. -/
theorem highPairWeight_nonneg (x h : ℝ) : 0 ≤ highPairWeight x h := by
  apply tsum_nonneg
  intro ρ
  split_ifs
  · apply mul_nonneg (by positivity)
    apply tsum_nonneg
    intro σ
    split_ifs <;> positivity
  · positivity

/-- The high pair count in BHMS page 19 final display, with log to the fourth.
All zero multiplicities and both ordinate ranges retain their paper meanings. -/
theorem high_pair_count : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      highPairWeight x h ≤ C * (h / x) * Real.log x ^ 4 := by
  classical
  obtain ⟨C, hC, hc⟩ := TailCount402.finite_high_pair_count
  refine ⟨C, hC, ?_⟩
  intro x h hx hh hhx
  let S := (PairKernel402.low_zeros_finite x (by linarith : 0 ≤ x)).toFinset
  let H := S.filter (fun ρ => x / h < |ρ.1.im|)
  have hS (ρ : NontrivialZero) : ρ ∈ S ↔ |ρ.1.im| ≤ x := Set.Finite.mem_toFinset _
  have hH (ρ : NontrivialZero) : ρ ∈ H ↔ x / h < |ρ.1.im| ∧ |ρ.1.im| ≤ x := by
    simp only [H, mem_filter, hS, and_comm]
  have hin (ρ : NontrivialZero) :
      (∑' σ : NontrivialZero, if |σ.1.im| ≤ x then
          (analyticOrderNatAt riemannZeta σ.1 : ℝ) / (1 + |ρ.1.im - σ.1.im|) else 0) =
      ∑ σ ∈ S, mz σ.1 / (1 + |ρ.1.im - σ.1.im|) := by
    rw [tsum_eq_sum (s := S) (fun σ hσ => by
      have hn : ¬ |σ.1.im| ≤ x := fun hh => hσ ((hS σ).mpr hh)
      exact if_neg hn)]
    apply sum_congr rfl
    intro σ hσ
    rw [if_pos ((hS σ).mp hσ)]
    rfl
  have he : highPairWeight x h = ∑ ρ ∈ H, (mz ρ.1 / |ρ.1.im| ^ 2) *
      (∑ σ ∈ S, mz σ.1 / (1 + |ρ.1.im - σ.1.im|)) := by
    unfold highPairWeight
    rw [tsum_eq_sum (s := H) (fun ρ hρ => if_neg (fun hh => hρ ((hH ρ).mpr hh)))]
    apply sum_congr rfl
    intro ρ hρ
    rw [if_pos ((hH ρ).mp hρ), hin]
    rfl
  rw [he]
  have hb := hc x h hx hh hhx (H.image (fun ρ => ρ.1)) (S.image (fun ρ => ρ.1))
    (by
      intro ρ hρ
      obtain ⟨σ, hσ, rfl⟩ := mem_image.mp hρ
      exact ⟨σ.2, ((hH σ).mp hσ).1⟩)
    (by
      intro ρ hρ
      obtain ⟨σ, hσ, rfl⟩ := mem_image.mp hρ
      exact ⟨σ.2, (hS σ).mp hσ⟩)
  unfold NontrivialZero at *
  have himage : (∑ ρ ∈ H.image (fun ρ => ρ.1), (mz ρ / |ρ.im| ^ 2) *
      (∑ σ ∈ S.image (fun σ => σ.1), mz σ / (1 + |ρ.im - σ.im|))) =
      ∑ ρ ∈ H, (mz ρ.1 / |ρ.1.im| ^ 2) *
      (∑ σ ∈ S, mz σ.1 / (1 + |ρ.1.im - σ.1.im|)) := by
    rw [sum_image Subtype.val_injective.injOn]
    apply sum_congr rfl
    intro ρ _
    rw [sum_image Subtype.val_injective.injOn]
  rw [himage] at hb
  exact hb

/-! ## 1. Integral of a complex power on a positive interval -/

private theorem hpi_pow_integral {c : ℂ} {x : ℝ} (hx : 1 ≤ x)
    (h0 : 0 ≤ c.re) (h2 : c.re ≤ 2) :
    ‖∫ t in x..(3 * x), ((t : ℝ) : ℂ) ^ c‖ ≤
      64 * x ^ (c.re + 1) / (1 + |c.im|) := by
  have hx0 : 0 < x := by linarith
  have hx3 : (0 : ℝ) < 3 * x := by linarith
  have hs : -1 < c.re := by linarith
  have hA : ∀ y : ℝ, 0 < y → ‖((y : ℝ) : ℂ) ^ (c + 1)‖ = y ^ (c.re + 1) := by
    intro y hy
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.add_re, Complex.one_re]
  have hden : (0 : ℝ) < 1 + |c.im| := by linarith [abs_nonneg c.im]
  have hpos1 : (0 : ℝ) < x ^ (c.re + 1) := Real.rpow_pos_of_pos hx0 _
  have habs : (0 : ℝ) ≤ |c.im| := abs_nonneg c.im
  rcases le_or_gt 1 |c.im| with hbig | hsmall
  · rw [integral_cpow (Or.inl hs)]
    have h2' : |c.im| ≤ ‖c + 1‖ := by
      have h : ‖c + 1‖ ≥ |(c + 1).im| := Complex.abs_im_le_norm _
      simpa only [Complex.add_im, Complex.one_im, add_zero] using h
    have hnum : ‖((3 * x : ℝ) : ℂ) ^ (c + 1) - ((x : ℝ) : ℂ) ^ (c + 1)‖ ≤
        (3 * x) ^ (c.re + 1) + x ^ (c.re + 1) := by
      refine (norm_sub_le _ _).trans ?_
      rw [hA (3 * x) hx3, hA x hx0]
    have hnorm : ‖(((3 * x : ℝ) : ℂ) ^ (c + 1) - ((x : ℝ) : ℂ) ^ (c + 1)) / (c + 1)‖ ≤
        ((3 * x) ^ (c.re + 1) + x ^ (c.re + 1)) / |c.im| := by
      rw [norm_div]
      exact div_le_div₀ (by positivity) hnum (by linarith) h2'
    refine hnorm.trans ?_
    have h3 : (3 * x) ^ (c.re + 1) = 3 ^ (c.re + 1) * x ^ (c.re + 1) := by
      rw [Real.mul_rpow (by norm_num) hx0.le]
    have h4 : (3 : ℝ) ^ (c.re + 1) ≤ 27 := by
      have h : (3 : ℝ) ^ (c.re + 1) ≤ (3 : ℝ) ^ (3 : ℝ) :=
        (Real.rpow_le_rpow_left_iff (by norm_num)).mpr (by linarith)
      have h27 : (3 : ℝ) ^ (3 : ℝ) = 27 := by norm_num
      linarith [h, h27]
    rw [h3]
    have hnum2 : 3 ^ (c.re + 1) * x ^ (c.re + 1) + x ^ (c.re + 1) ≤ 28 * x ^ (c.re + 1) := by
      nlinarith
    refine (div_le_div_of_nonneg_right hnum2 habs).trans ?_
    rw [div_le_div_iff₀ (by linarith : (0:ℝ) < |c.im|) hden]
    nlinarith [hpos1, habs, hbig]
  · have hpt : ∀ t ∈ Set.uIoc x (3 * x), ‖((t : ℝ) : ℂ) ^ c‖ ≤ (3 * x) ^ c.re := by
      intro t ht
      rw [Set.uIoc_of_le (by linarith : x ≤ 3 * x)] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      exact Real.rpow_le_rpow ht0.le ht.2 h0
    have hmono : ‖∫ t in x..(3 * x), ((t : ℝ) : ℂ) ^ c‖ ≤
        (3 * x) ^ c.re * (3 * x - x) := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := 3 * x) hpt
      calc _ ≤ (3 * x) ^ c.re * |3 * x - x| := this
        _ = _ := by rw [abs_of_pos (by linarith : (0:ℝ) < 3 * x - x)]
    refine hmono.trans ?_
    have h3 : (3 * x) ^ c.re = 3 ^ c.re * x ^ c.re := by
      rw [Real.mul_rpow (by norm_num) hx0.le]
    have h4 : (3 : ℝ) ^ c.re ≤ 9 := by
      have h : (3 : ℝ) ^ c.re ≤ (3 : ℝ) ^ (2 : ℝ) :=
        (Real.rpow_le_rpow_left_iff (by norm_num)).mpr h2
      have h9 : (3 : ℝ) ^ (2 : ℝ) = 9 := by norm_num
      linarith [h, h9]
    rw [h3]
    have hb : 3 ^ c.re * x ^ c.re * (3 * x - x) ≤ 18 * x ^ (c.re + 1) := by
      have hsp : x ^ c.re * x = x ^ (c.re + 1) := (Real.rpow_add_one hx0.ne' c.re).symm
      nlinarith [Real.rpow_pos_of_pos hx0 c.re]
    refine hb.trans ?_
    rw [le_div_iff₀ hden]
    have hden2 : (1:ℝ) ≤ 1 + |c.im| := by linarith
    nlinarith [hpos1, hden2, hsmall, habs]

/-! ## 2. Real part of an interval integral -/

private theorem hpi_re_interval {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, (f t).re) = (∫ t in a..b, f t).re := by
  have hf' : Integrable f (volume.restrict (Set.Ioc a b)) := hf.1
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  exact integral_re hf'

/-! ## 3. Norm square of a finite sum -/

private theorem hpi_re_sum {ι : Type*} [DecidableEq ι] (H : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ H, f i).re = ∑ i ∈ H, (f i).re := by
  induction H using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Complex.add_re, ih]

private theorem hpi_norm_sq_sum {ι : Type*} [DecidableEq ι] (H : Finset ι) (b : ι → ℂ) :
    ‖∑ i ∈ H, b i‖ ^ 2 = ∑ i ∈ H, ∑ j ∈ H, (b i * star (b j)).re := by
  have h1 : (∑ i ∈ H, b i) * star (∑ j ∈ H, b j) = ((‖∑ i ∈ H, b i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hstar : star (∑ j ∈ H, b j) = ∑ j ∈ H, star (b j) := by
    rw [Complex.star_def]
    exact map_sum _ _ _
  rw [hstar, Finset.sum_mul_sum] at h1
  have h2 := congrArg Complex.re h1
  rw [Complex.ofReal_re, hpi_re_sum] at h2
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ H) => hpi_re_sum H (fun j => b i * star (b j)))] at h2
  exact h2.symm

/-! ## 4. The AM-GM comparison of the reciprocal ordinate products -/

private theorem hpi_recip_le {ι : Type*} (H : Finset ι) (A gp : ι → ℝ) (K : ι → ι → ℝ)
    (hA : ∀ i ∈ H, 0 ≤ A i) (hg : ∀ i ∈ H, 0 < gp i)
    (hK : ∀ i ∈ H, ∀ j ∈ H, 0 ≤ K i j) (hKs : ∀ i ∈ H, ∀ j ∈ H, K i j = K j i) :
    ∑ i ∈ H, ∑ j ∈ H, A i * A j / (gp i * gp j) * K i j ≤
      ∑ i ∈ H, (A i / gp i ^ 2) * ∑ j ∈ H, A j * K i j := by
  have hpt : ∀ i ∈ H, ∀ j ∈ H, A i * A j / (gp i * gp j) * K i j ≤
      (1 / 2) * (A i * A j / gp i ^ 2 * K i j) +
        (1 / 2) * (A i * A j / gp j ^ 2 * K i j) := by
    intro i hi j hj
    have hi0 := hA i hi
    have hj0 := hA j hj
    have hgi : 0 < gp i := hg i hi
    have hgj : 0 < gp j := hg j hj
    have hk := hK i hi j hj
    have h2 : A i * A j / (gp i * gp j) * 2 ≤ A i * A j / gp i ^ 2 + A i * A j / gp j ^ 2 := by
      have key : A i * A j / gp i ^ 2 + A i * A j / gp j ^ 2 -
          A i * A j / (gp i * gp j) * 2 =
          A i * A j * (gp i - gp j) ^ 2 / (gp i ^ 2 * gp j ^ 2) := by
        field_simp
        ring
      have hnn : 0 ≤ A i * A j * (gp i - gp j) ^ 2 / (gp i ^ 2 * gp j ^ 2) := by
        apply div_nonneg
        · exact mul_nonneg (mul_nonneg hi0 hj0) (sq_nonneg _)
        · positivity
      linarith [key ▸ hnn]
    have hm := mul_le_mul_of_nonneg_right h2 hk
    have e : (A i * A j / gp i ^ 2 + A i * A j / gp j ^ 2) * K i j =
        A i * A j / gp i ^ 2 * K i j + A i * A j / gp j ^ 2 * K i j := by ring
    rw [e] at hm
    linarith
  refine (sum_le_sum (fun i hi => sum_le_sum (fun j hj => hpt i hi j hj))).trans (le_of_eq ?_)
  have hsplit : ∑ i ∈ H, ∑ j ∈ H, ((1 / 2) * (A i * A j / gp i ^ 2 * K i j) +
        (1 / 2) * (A i * A j / gp j ^ 2 * K i j)) =
      (∑ i ∈ H, ∑ j ∈ H, (1 / 2) * (A i * A j / gp i ^ 2 * K i j)) +
      (∑ i ∈ H, ∑ j ∈ H, (1 / 2) * (A i * A j / gp j ^ 2 * K i j)) := by
    simp only [Finset.sum_add_distrib]
  rw [hsplit]
  have hT1 : ∑ i ∈ H, ∑ j ∈ H, (1 / 2) * (A i * A j / gp i ^ 2 * K i j) =
      (1 / 2) * ∑ i ∈ H, (A i / gp i ^ 2) * ∑ j ∈ H, A j * K i j := by
    rw [Finset.mul_sum]
    refine sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, mul_sum]
    refine sum_congr rfl (fun j _ => ?_)
    ring
  have hT2 : ∑ i ∈ H, ∑ j ∈ H, (1 / 2) * (A i * A j / gp j ^ 2 * K i j) =
      (1 / 2) * ∑ i ∈ H, (A i / gp i ^ 2) * ∑ j ∈ H, A j * K i j := by
    have hcomm : ∑ i ∈ H, ∑ j ∈ H, (1 / 2) * (A i * A j / gp j ^ 2 * K i j) =
        ∑ j ∈ H, ∑ i ∈ H, (1 / 2) * (A i * A j / gp j ^ 2 * K i j) := Finset.sum_comm
    rw [hcomm, Finset.mul_sum]
    refine sum_congr rfl (fun j hj => ?_)
    have hswap : ∑ i ∈ H, (1 / 2) * (A i * A j / gp j ^ 2 * K i j) =
        ∑ i ∈ H, (1 / 2) * (A i * A j / gp j ^ 2 * K j i) :=
      sum_congr rfl (fun i hi => by rw [hKs i hi j hj])
    rw [hswap, Finset.mul_sum, mul_sum]
    refine sum_congr rfl (fun i _ => ?_)
    ring
  rw [hT1, hT2]
  ring

/-! ## 5. Pair integral bound -/

private theorem hpi_pair_integral {A B : ℝ} {p q : ℂ} {x : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : p ≠ 0) (hq : q ≠ 0) (hx : 1 ≤ x)
    (hp0 : 0 ≤ p.re) (hq0 : 0 ≤ q.re) (hpq : p.re + q.re ≤ 2) :
    ‖∫ t in x..(3 * x), ((A : ℂ) * ((t : ℝ) : ℂ) ^ p / p) *
        star ((B : ℂ) * ((t : ℝ) : ℂ) ^ q / q)‖ ≤
      A * B / (‖p‖ * ‖q‖) * (64 * x ^ (p.re + q.re + 1) / (1 + |p.im - q.im|)) := by
  have hx0 : 0 < x := by linarith
  have hconj : ∀ t : ℝ, 0 < t →
      (starRingEnd ℂ) (((t : ℝ) : ℂ) ^ q) = ((t : ℝ) : ℂ) ^ ((starRingEnd ℂ) q) := by
    intro t ht
    have h := Complex.cpow_conj (((t : ℝ) : ℂ)) q (by
      rw [Complex.arg_ofReal_of_nonneg ht.le]; exact Real.pi_ne_zero.symm)
    rw [show (starRingEnd ℂ) (((t : ℝ) : ℂ)) = ((t : ℝ) : ℂ) from Complex.conj_ofReal t] at h
    exact h.symm
  have hpt : ∀ t ∈ Set.uIcc x (3 * x),
      ((A : ℂ) * ((t : ℝ) : ℂ) ^ p / p) * star ((B : ℂ) * ((t : ℝ) : ℂ) ^ q / q) =
      ((A * B : ℝ) : ℂ) / (p * star q) * ((t : ℝ) : ℂ) ^ (p + star q) := by
    intro t ht
    rw [Set.mem_uIcc] at ht
    have ht0 : 0 < t := by rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have htne : ((t : ℝ) : ℂ) ≠ 0 := by
      simp only [Ne, Complex.ofReal_eq_zero]; linarith
    have hstar : star ((B : ℂ) * ((t : ℝ) : ℂ) ^ q / q) =
        (B : ℂ) * ((t : ℝ) : ℂ) ^ (star q) / star q := by
      rw [Complex.star_def, map_div₀, map_mul, Complex.conj_ofReal, hconj t ht0]
    rw [hstar, Complex.cpow_add _ _ htne]
    have hq' : (starRingEnd ℂ) q ≠ 0 := by simpa using hq
    field_simp
    push_cast
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul, norm_mul]
  have hconst : ‖((A * B : ℝ) : ℂ) / (p * star q)‖ = A * B / (‖p‖ * ‖q‖) := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA hB)]
    rw [Complex.star_def, Complex.norm_conj]
  rw [hconst]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hb := hpi_pow_integral (c := p + star q) (x := x) hx
    (by simp; linarith)
    (by simp; linarith)
  rwa [show (p + star q).re = p.re + q.re from by simp,
    show (p + star q).im = p.im - q.im from by simp [sub_eq_add_neg]] at hb

/-! ## 6. The `L²` bound for a finite zero sum -/

private theorem hpi_sum_integral {ι : Type*} (H : Finset ι) (A : ι → ℝ) (c : ι → ℂ)
    {x S : ℝ} (hx : 1 ≤ x) (hA : ∀ i ∈ H, 0 ≤ A i)
    (hcne : ∀ i ∈ H, c i ≠ 0) (hre0 : ∀ i ∈ H, 0 ≤ (c i).re)
    (hS : ∀ i ∈ H, ∀ j ∈ H, (c i).re + (c j).re ≤ S) (hS0 : 0 ≤ S) (hS2 : S ≤ 2) :
    ∫ t in x..(3 * x), ‖∑ i ∈ H, (A i : ℂ) * ((t : ℝ) : ℂ) ^ (c i) / c i‖ ^ 2 ≤
      64 * x ^ (S + 1) * ∑ i ∈ H, (A i / ‖c i‖ ^ 2) *
        ∑ j ∈ H, A j / (1 + |(c i).im - (c j).im|) := by
  classical
  have hx0 : 0 < x := by linarith
  have hsub : Set.uIcc x (3 * x) ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    rw [Set.mem_uIcc] at ht
    refine Set.mem_Ioi.mpr ?_
    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  have hpow : ∀ i, ContinuousOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (c i)) (Set.uIcc x (3 * x)) := by
    intro i
    have hI : ContinuousOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (c i)) (Set.Ioi (0 : ℝ)) := by
      intro t ht
      exact (Complex.continuousAt_ofReal_cpow_const t (c i)
        (Or.inr (ne_of_gt ht))).continuousWithinAt
    exact hI.mono hsub
  have hcontb : ∀ i, ContinuousOn (fun t : ℝ => (A i : ℂ) * ((t : ℝ) : ℂ) ^ (c i) / c i)
      (Set.uIcc x (3 * x)) := by
    intro i
    exact (continuousOn_const.mul (hpow i)).div_const _
  have hcontF : ∀ i j, ContinuousOn (fun t : ℝ =>
      ((A i : ℂ) * ((t : ℝ) : ℂ) ^ (c i) / c i) *
        star ((A j : ℂ) * ((t : ℝ) : ℂ) ^ (c j) / c j)) (Set.uIcc x (3 * x)) := by
    intro i j
    exact (hcontb i).mul (hcontb j).star
  have hIntF : ∀ i j, IntervalIntegrable (fun t : ℝ =>
      ((A i : ℂ) * ((t : ℝ) : ℂ) ^ (c i) / c i) *
        star ((A j : ℂ) * ((t : ℝ) : ℂ) ^ (c j) / c j)) volume x (3 * x) :=
    fun i j => (hcontF i j).intervalIntegrable
  have hcongr : ∀ t ∈ Set.uIcc x (3 * x),
      ‖∑ i ∈ H, (A i : ℂ) * ((t : ℝ) : ℂ) ^ (c i) / c i‖ ^ 2 =
      ∑ i ∈ H, ∑ j ∈ H, (((A i : ℂ) * ((t : ℝ) : ℂ) ^ (c i) / c i) *
        star ((A j : ℂ) * ((t : ℝ) : ℂ) ^ (c j) / c j)).re :=
    fun t _ => hpi_norm_sq_sum H _
  rw [intervalIntegral.integral_congr hcongr]
  have hIntRe : ∀ i j, IntervalIntegrable (fun t : ℝ =>
      (((A i : ℂ) * ((t : ℝ) : ℂ) ^ (c i) / c i) *
        star ((A j : ℂ) * ((t : ℝ) : ℂ) ^ (c j) / c j)).re) volume x (3 * x) :=
    fun i j => (Complex.continuous_re.comp_continuousOn (hcontF i j)).intervalIntegrable
  have hIntOuter : ∀ i ∈ H, IntervalIntegrable (fun t : ℝ => ∑ j ∈ H,
      (((A i : ℂ) * ((t : ℝ) : ℂ) ^ (c i) / c i) *
        star ((A j : ℂ) * ((t : ℝ) : ℂ) ^ (c j) / c j)).re) volume x (3 * x) :=
    fun i _ => (continuousOn_finsetSum H (fun j _ =>
      Complex.continuous_re.comp_continuousOn (hcontF i j))).intervalIntegrable
  rw [intervalIntegral.integral_finsetSum hIntOuter]
  rw [Finset.sum_congr rfl (fun i _ => intervalIntegral.integral_finsetSum (fun j _ => hIntRe i j))]
  have h1 : ∑ i ∈ H, ∑ j ∈ H, (∫ t in x..(3 * x),
        (((A i : ℂ) * ((t : ℝ) : ℂ) ^ (c i) / c i) *
          star ((A j : ℂ) * ((t : ℝ) : ℂ) ^ (c j) / c j)).re) ≤
      ∑ i ∈ H, ∑ j ∈ H, (A i * A j / (‖c i‖ * ‖c j‖) *
        (64 * x ^ ((c i).re + (c j).re + 1) / (1 + |(c i).im - (c j).im|))) := by
    refine sum_le_sum (fun i hi => sum_le_sum (fun j hj => ?_))
    rw [hpi_re_interval (by linarith) (hIntF i j)]
    exact (Complex.re_le_norm _).trans (hpi_pair_integral (hA i hi) (hA j hj)
      (hcne i hi) (hcne j hj) hx (hre0 i hi) (hre0 j hj) (le_trans (hS i hi j hj) hS2))
  have h2 : ∑ i ∈ H, ∑ j ∈ H, (A i * A j / (‖c i‖ * ‖c j‖) *
        (64 * x ^ ((c i).re + (c j).re + 1) / (1 + |(c i).im - (c j).im|))) ≤
      64 * x ^ (S + 1) * ∑ i ∈ H, (A i / ‖c i‖ ^ 2) *
        ∑ j ∈ H, A j / (1 + |(c i).im - (c j).im|) := by
    have hpull : ∑ i ∈ H, ∑ j ∈ H, 64 * x ^ (S + 1) * (A i * A j / (‖c i‖ * ‖c j‖) *
        (1 / (1 + |(c i).im - (c j).im|))) =
        64 * x ^ (S + 1) * ∑ i ∈ H, ∑ j ∈ H, (A i * A j / (‖c i‖ * ‖c j‖) *
          (1 / (1 + |(c i).im - (c j).im|))) := by
      rw [Finset.mul_sum]
      refine sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
    have hstep : ∑ i ∈ H, ∑ j ∈ H, (A i * A j / (‖c i‖ * ‖c j‖) *
        (64 * x ^ ((c i).re + (c j).re + 1) / (1 + |(c i).im - (c j).im|))) ≤
        ∑ i ∈ H, ∑ j ∈ H, 64 * x ^ (S + 1) * (A i * A j / (‖c i‖ * ‖c j‖) *
          (1 / (1 + |(c i).im - (c j).im|))) := by
      refine sum_le_sum (fun i hi => sum_le_sum (fun j hj => ?_))
      have hexp : (c i).re + (c j).re + 1 ≤ S + 1 := by linarith [hS i hi j hj]
      have hxp : x ^ ((c i).re + (c j).re + 1) ≤ x ^ (S + 1) :=
        Real.rpow_le_rpow_of_exponent_le hx hexp
      have hnn : (0 : ℝ) ≤ A i * A j / (‖c i‖ * ‖c j‖) := by
        have h1 := hA i hi
        have h2 := hA j hj
        have h3 : (0:ℝ) < ‖c i‖ := norm_pos_iff.mpr (hcne i hi)
        have h4 : (0:ℝ) < ‖c j‖ := norm_pos_iff.mpr (hcne j hj)
        positivity
      have hden : (0 : ℝ) < 1 + |(c i).im - (c j).im| := by positivity
      have e1 : A i * A j / (‖c i‖ * ‖c j‖) *
          (64 * x ^ ((c i).re + (c j).re + 1) / (1 + |(c i).im - (c j).im|)) =
          64 * (A i * A j / (‖c i‖ * ‖c j‖)) * x ^ ((c i).re + (c j).re + 1) /
            (1 + |(c i).im - (c j).im|) := by ring
      have e2 : 64 * x ^ (S + 1) * (A i * A j / (‖c i‖ * ‖c j‖) *
          (1 / (1 + |(c i).im - (c j).im|))) =
          64 * (A i * A j / (‖c i‖ * ‖c j‖)) * x ^ (S + 1) /
            (1 + |(c i).im - (c j).im|) := by
        field_simp
      rw [e1, e2]
      apply div_le_div_of_nonneg_right _ hden.le
      exact mul_le_mul_of_nonneg_left hxp (by positivity)
    refine hstep.trans ?_
    rw [hpull]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hmain := hpi_recip_le H A (fun i => ‖c i‖)
      (fun i j => 1 / (1 + |(c i).im - (c j).im|)) hA
      (fun i hi => norm_pos_iff.mpr (hcne i hi))
      (fun i _ j _ => by positivity)
      (fun i _ j _ => by rw [abs_sub_comm])
    refine hmain.trans (le_of_eq ?_)
    refine sum_congr rfl (fun i _ => ?_)
    congr 1
    refine sum_congr rfl (fun j _ => ?_)
    ring
  exact h1.trans h2

/-- LEAF. BHMS pages 18 and 19, ignore the high increment difference and expand its square.
Integrate the complex powers, compare the two reciprocal ordinate factors by squares,
and use symmetry to obtain the asymmetric high kernel. This contains no tail count. -/
theorem high_pair_integral : 1 / 2 < Theta → Theta < 1 → ∃ K : ℝ, 0 ≤ K ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      IntervalIntegrable (fun t => ‖highZeros x h t‖ ^ 2) volume x (2 * x) ∧
      (∫ t in x..(2 * x), ‖highZeros x h t‖ ^ 2) ≤
        K * x ^ (2 * Theta + 1) * highPairWeight x h := by

  intro hlo hhi
  refine ⟨256, by norm_num, ?_⟩
  intro x h hx hh hhx
  classical
  have hx0 : 0 < x := by linarith
  have hh0 : 0 < h := by linarith
  let S : Finset NontrivialZero := (LeanLab.GoldbachAverage.PairKernel402.low_zeros_finite x hx0.le).toFinset
  let B : Finset NontrivialZero := S.filter (fun ρ => x / h < |ρ.1.im|)
  have hS : ∀ ρ : NontrivialZero, ρ ∈ S ↔ |ρ.1.im| ≤ x := fun ρ => Set.Finite.mem_toFinset _
  have hB : ∀ ρ : NontrivialZero, ρ ∈ B ↔ x / h < |ρ.1.im| ∧ |ρ.1.im| ≤ x := by
    intro ρ
    simp only [B, mem_filter, hS, and_comm]
  set T : ℝ → ℂ := fun u => ∑ ρ ∈ B, (mz ρ.1 : ℂ) * ((u : ℝ) : ℂ) ^ ρ.1 / ρ.1 with hTdef
  have hZ : ∀ t : ℝ, highZeros x h t = T (t + h) - T t := by
    intro t
    rw [highZeros, zeroSum]
    rw [tsum_eq_sum (s := B) (fun ρ hρ => by
      rw [if_neg (fun hh' => hρ ((hB ρ).mpr hh'))]
      simp)]
    simp only [hTdef]
    rw [← Finset.sum_sub_distrib]
    refine sum_congr rfl (fun ρ hρ => ?_)
    rw [if_pos ((hB ρ).mp hρ)]
    simp only [mz]
    push_cast
    ring
  have hcontTerm : ∀ ρ : NontrivialZero, ContinuousOn
      (fun u : ℝ => (mz ρ.1 : ℂ) * ((u : ℝ) : ℂ) ^ ρ.1 / ρ.1) (Set.Ioi 0) := by
    intro ρ
    have hp : ContinuousOn (fun u : ℝ => ((u : ℝ) : ℂ) ^ ρ.1) (Set.Ioi 0) := by
      intro u hu
      exact (Complex.continuousAt_ofReal_cpow_const u ρ.1 (Or.inr (ne_of_gt hu))).continuousWithinAt
    exact (continuousOn_const.mul hp).div_const _
  have hcontT : ContinuousOn T (Set.Ioi 0) := by
    rw [hTdef]
    exact continuousOn_finsetSum B (fun ρ _ => hcontTerm ρ)
  have hcontTn : ContinuousOn (fun u : ℝ => ‖T u‖ ^ 2) (Set.Ioi 0) := (hcontT.norm).pow 2
  have monoI : ∀ {a b : ℝ}, 0 < a → a ≤ b → Set.uIcc a b ⊆ Set.Ioi (0 : ℝ) := by
    intro a b ha hab t ht
    rw [Set.mem_uIcc] at ht
    obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := ht
    · exact Set.mem_Ioi.mpr (by linarith)
    · exact Set.mem_Ioi.mpr (by linarith)
  have hcontHz : ContinuousOn (fun t : ℝ => highZeros x h t) (Set.Ioi 0) := by
    have h1 : ContinuousOn (fun t : ℝ => T (t + h)) (Set.Ioi 0) :=
      hcontT.comp (by fun_prop : Continuous fun t : ℝ => t + h).continuousOn
        (fun t ht => by
          simp only [Set.mem_Ioi] at ht ⊢
          linarith)
    exact (h1.sub hcontT).congr (fun t _ => hZ t)
  have hIntT : ∀ a b : ℝ, 0 < a → a ≤ b →
      IntervalIntegrable (fun u : ℝ => ‖T u‖ ^ 2) volume a b :=
    fun a b ha hab => (hcontTn.mono (monoI ha hab)).intervalIntegrable
  have hIntZ : IntervalIntegrable (fun t : ℝ => ‖highZeros x h t‖ ^ 2) volume x (2 * x) :=
    ((hcontHz.norm.pow 2).mono (monoI hx0 (by linarith))).intervalIntegrable
  refine ⟨hIntZ, ?_⟩
  have hT3 := hIntT x (3 * x) hx0 (by linarith)
  have hIntShift : IntervalIntegrable (fun t : ℝ => ‖T (t + h)‖ ^ 2) volume x (2 * x) := by
    have hc : ContinuousOn (fun t : ℝ => ‖T (t + h)‖ ^ 2) (Set.uIcc x (2 * x)) :=
      hcontTn.comp (by fun_prop : Continuous fun t : ℝ => t + h).continuousOn
        (fun t ht => by
          simp only [Set.mem_uIcc] at ht
          obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := ht
          · simp only [Set.mem_Ioi]; linarith
          · simp only [Set.mem_Ioi]; linarith)
    exact hc.intervalIntegrable
  have hpt : ∀ t : ℝ, ‖highZeros x h t‖ ^ 2 ≤ 2 * ‖T (t + h)‖ ^ 2 + 2 * ‖T t‖ ^ 2 := by
    intro t
    rw [hZ t]
    have h1 : ‖T (t + h) - T t‖ ≤ ‖T (t + h)‖ + ‖T t‖ := norm_sub_le _ _
    have h2 : (‖T (t + h)‖ + ‖T t‖) ^ 2 ≤ 2 * ‖T (t + h)‖ ^ 2 + 2 * ‖T t‖ ^ 2 := by
      nlinarith [sq_nonneg (‖T (t + h)‖ - ‖T t‖)]
    calc ‖T (t + h) - T t‖ ^ 2 ≤ (‖T (t + h)‖ + ‖T t‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  have hIntR : IntervalIntegrable (fun t : ℝ => 2 * ‖T (t + h)‖ ^ 2 + 2 * ‖T t‖ ^ 2)
      volume x (2 * x) :=
    (hIntShift.const_mul 2).add ((hIntT x (2 * x) hx0 (by linarith)).const_mul 2)
  have hstep1 : (∫ t in x..(2 * x), ‖highZeros x h t‖ ^ 2) ≤
      ∫ t in x..(2 * x), (2 * ‖T (t + h)‖ ^ 2 + 2 * ‖T t‖ ^ 2) :=
    intervalIntegral.integral_mono_on (by linarith) hIntZ hIntR (fun t _ => hpt t)
  have hEq1 : (∫ t in x..(2 * x), ‖T (t + h)‖ ^ 2) = ∫ u in (x + h)..(2 * x + h), ‖T u‖ ^ 2 := by
    have := intervalIntegral.integral_comp_add_right (f := fun u : ℝ => ‖T u‖ ^ 2) (a := x)
      (b := 2 * x) h
    simpa using this
  have hle1 : (∫ u in (x + h)..(2 * x + h), ‖T u‖ ^ 2) ≤ ∫ u in x..(3 * x), ‖T u‖ ^ 2 :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall (fun u => sq_nonneg ‖T u‖)) hT3
  have hle2 : (∫ u in x..(2 * x), ‖T u‖ ^ 2) ≤ ∫ u in x..(3 * x), ‖T u‖ ^ 2 :=
    intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (Filter.Eventually.of_forall (fun u => sq_nonneg ‖T u‖)) hT3
  have hsplit : (∫ t in x..(2 * x), (2 * ‖T (t + h)‖ ^ 2 + 2 * ‖T t‖ ^ 2)) =
      2 * (∫ t in x..(2 * x), ‖T (t + h)‖ ^ 2) +
        2 * (∫ t in x..(2 * x), ‖T t‖ ^ 2) := by
    rw [intervalIntegral.integral_add (hIntShift.const_mul 2)
        ((hIntT x (2 * x) hx0 (by linarith)).const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hbound3 : (∫ u in x..(3 * x), ‖T u‖ ^ 2) ≤
      64 * x ^ (2 * Theta + 1) * ∑ ρ ∈ B, (mz ρ.1 / ‖ρ.1‖ ^ 2) *
        ∑ σ ∈ B, mz σ.1 / (1 + |ρ.1.im - σ.1.im|) := by
    have h := hpi_sum_integral (H := B) (A := fun ρ : NontrivialZero => mz ρ.1)
      (c := fun ρ : NontrivialZero => ρ.1) (x := x) (S := 2 * Theta)
      (by linarith) (fun ρ _ => mz_nonneg ρ.1)
      (fun ρ _ => by
        intro hzero
        have := ρ.2.2.1
        rw [hzero] at this
        simp at this)
      (fun ρ _ => le_of_lt ρ.2.2.1)
      (fun ρ _ σ _ => by
        have h1 := LeanLab.GoldbachAverage.GSCor2.re_le_Theta ρ
        have h2 := LeanLab.GoldbachAverage.GSCor2.re_le_Theta σ
        linarith)
      (by linarith) (by linarith)
    simpa only [hTdef] using h
  have hw : ∑ ρ ∈ B, (mz ρ.1 / ‖ρ.1‖ ^ 2) * ∑ σ ∈ B, mz σ.1 / (1 + |ρ.1.im - σ.1.im|)
      ≤ highPairWeight x h := by
    have he : highPairWeight x h = ∑ ρ ∈ B, (mz ρ.1 / |ρ.1.im| ^ 2) *
        (∑ σ ∈ S, mz σ.1 / (1 + |ρ.1.im - σ.1.im|)) := by
      rw [highPairWeight]
      rw [tsum_eq_sum (s := B) (fun ρ hρ => by
        rw [if_neg (fun hh' => hρ ((hB ρ).mpr hh'))])]
      refine sum_congr rfl (fun ρ hρ => ?_)
      rw [if_pos ((hB ρ).mp hρ)]
      congr 1
      rw [tsum_eq_sum (s := S) (fun σ hσ => by
        have hnot : ¬ |σ.1.im| ≤ x := fun hle => hσ ((hS σ).mpr hle)
        simp only [hnot, ite_false])]
      refine sum_congr rfl (fun σ hσ => ?_)
      rw [if_pos ((hS σ).mp hσ)]
      simp only [mz]
    rw [he]
    refine sum_le_sum (fun ρ hρ => ?_)
    have him : |ρ.1.im| ≤ ‖ρ.1‖ := Complex.abs_im_le_norm _
    have hxh : (0:ℝ) < x / h := div_pos hx0 hh0
    have him0 : (0:ℝ) < |ρ.1.im| := by linarith [(hB ρ).mp hρ |>.1]
    have hinv : mz ρ.1 / ‖ρ.1‖ ^ 2 ≤ mz ρ.1 / |ρ.1.im| ^ 2 := by
      have hsq : |ρ.1.im| ^ 2 ≤ ‖ρ.1‖ ^ 2 := by nlinarith
      exact div_le_div_of_nonneg_left (mz_nonneg _) (by positivity) hsq
    have hinner : (∑ σ ∈ B, mz σ.1 / (1 + |ρ.1.im - σ.1.im|)) ≤
        ∑ σ ∈ S, mz σ.1 / (1 + |ρ.1.im - σ.1.im|) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun σ _ _ => div_nonneg (mz_nonneg _) (by positivity))
    refine mul_le_mul hinv hinner (Finset.sum_nonneg (fun σ _ =>
      div_nonneg (mz_nonneg _) (by positivity))) ?_
    exact div_nonneg (mz_nonneg _) (by positivity)
  calc (∫ t in x..(2 * x), ‖highZeros x h t‖ ^ 2)
      ≤ 4 * (∫ u in x..(3 * x), ‖T u‖ ^ 2) := by
        rw [hsplit] at hstep1
        nlinarith [hstep1, hEq1, hle1, hle2]
    _ ≤ 4 * (64 * x ^ (2 * Theta + 1) * ∑ ρ ∈ B, (mz ρ.1 / ‖ρ.1‖ ^ 2) *
        ∑ σ ∈ B, mz σ.1 / (1 + |ρ.1.im - σ.1.im|)) := by
        linarith [hbound3]
    _ ≤ 256 * x ^ (2 * Theta + 1) * highPairWeight x h := by
        have hxp : (0:ℝ) < x ^ (2 * Theta + 1) := Real.rpow_pos_of_pos hx0 _
        nlinarith [hw, hxp, mul_le_mul_of_nonneg_left hw hxp.le]


/-- The exact high_zero_variance target follows from the integrated kernel and its proved count.
CONDITIONAL ON high_pair_integral. -/
theorem high_zero_variance_assembled : 1 / 2 < Theta → Theta < 1 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      IntervalIntegrable (fun t => ‖highZeros x h t‖ ^ 2) volume x (2 * x) ∧
      (∫ t in x..(2 * x), ‖highZeros x h t‖ ^ 2) ≤
        C * h * x ^ (2 * Theta) * Real.log x ^ 4 := by
  intro hlo hhi
  obtain ⟨K, hK, hk⟩ := high_pair_integral hlo hhi
  obtain ⟨C, hC, hc⟩ := high_pair_count
  refine ⟨K * C, by positivity, ?_⟩
  intro x h hx hh hhx
  obtain ⟨hi, hb⟩ := hk x h hx hh hhx
  refine ⟨hi, hb.trans ?_⟩
  have hx0 : 0 < x := by linarith
  have hp : x ^ (2 * Theta + 1) = x ^ (2 * Theta) * x := by
    rw [Real.rpow_add hx0, Real.rpow_one]
  have hm := mul_le_mul_of_nonneg_left (hc x h hx hh hhx)
    (show 0 ≤ K * x ^ (2 * Theta + 1) by positivity)
  calc _ ≤ (K * x ^ (2 * Theta + 1)) * (C * (h / x) * Real.log x ^ 4) := hm
    _ = _ := by rw [hp]; field_simp

example : type_of% high_zero_variance = type_of% high_zero_variance_assembled := rfl

end LeanLab.GoldbachAverage.Decomp402f

import Mathlib

open scoped ContDiff ENNReal
open MeasureTheory Set

namespace NavierStokes

/-- Physical space `ℝ³` with its Euclidean norm. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- `j`-th partial derivative. -/
noncomputable def pd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : Fin 3) (g : E3 → F) (x : E3) : F :=
  fderiv ℝ g x (EuclideanSpace.single j (1 : ℝ))

/-- Laplacian. -/
noncomputable def lap (g : E3 → ℝ) (x : E3) : ℝ := ∑ j : Fin 3, pd j (pd j g) x

/-- Divergence. -/
noncomputable def div (v : E3 → E3) (x : E3) : ℝ := ∑ j : Fin 3, pd j (fun y => v y j) x

/-- Time derivative on `[0, ∞)`. -/
noncomputable def dt (g : ℝ → ℝ) (t : ℝ) : ℝ := derivWithin g (Ici 0) t

/-- Space-time domain. -/
def spaceTime : Set (ℝ × E3) := Ici (0 : ℝ) ×ˢ (univ : Set E3)

def SchwartzDecay (u0 : E3 → E3) : Prop :=
  ∀ n K : ℕ, ∃ C : ℝ, ∀ x : E3, ‖iteratedFDeriv ℝ n u0 x‖ ≤ C / (1 + ‖x‖) ^ K

def ForcingDecay (f : ℝ → E3 → E3) : Prop :=
  ∀ n K : ℕ, ∃ C : ℝ, ∀ z ∈ spaceTime,
    ‖iteratedFDerivWithin ℝ n (fun z : ℝ × E3 => f z.1 z.2) spaceTime z‖
      ≤ C / (1 + ‖z.2‖ + z.1) ^ K

structure SatisfiesNSEquations (ν : ℝ) (f u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ) : Prop where
  momentum : ∀ t : ℝ, 0 ≤ t → ∀ (x : E3) (i : Fin 3),
    dt (fun s => u s x i) t + ∑ j : Fin 3, u t x j * pd j (fun y => u t y i) x
      = ν * lap (fun y => u t y i) x - pd i (p t) x + f t x i
  incompressible : ∀ t : ℝ, 0 ≤ t → ∀ x : E3, div (u t) x = 0

structure IsSmoothNSSolution (ν : ℝ) (f : ℝ → E3 → E3) (u0 : E3 → E3)
    (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ) : Prop
    extends SatisfiesNSEquations ν f u p where
  smooth_u : ContDiffOn ℝ ∞ (fun z : ℝ × E3 => u z.1 z.2) spaceTime
  smooth_p : ContDiffOn ℝ ∞ (fun z : ℝ × E3 => p z.1 z.2) spaceTime
  initial : ∀ x : E3, u 0 x = u0 x

def BoundedEnergy (u : ℝ → E3 → E3) : Prop :=
  ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∫⁻ x : E3, ‖u t x‖ₑ ^ 2 < ENNReal.ofReal C

structure IsNSSolution (ν : ℝ) (f : ℝ → E3 → E3) (u0 : E3 → E3)
    (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ) : Prop
    extends IsSmoothNSSolution ν f u0 u p where
  bounded_energy : BoundedEnergy u

def AdmissibleInitialDatum (u0 : E3 → E3) : Prop :=
  ContDiff ℝ ∞ u0 ∧ (∀ x, div u0 x = 0) ∧ SchwartzDecay u0

def AdmissibleForcing (f : ℝ → E3 → E3) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × E3 => f z.1 z.2) spaceTime ∧ ForcingDecay f

def StatementA (ν : ℝ) : Prop :=
  ∀ u0 : E3 → E3, AdmissibleInitialDatum u0 →
    ∃ (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ), IsNSSolution ν (fun _ _ => 0) u0 u p

def NavierStokesExistenceAndSmoothness : Prop := ∀ ν : ℝ, 0 < ν → StatementA ν

def StatementC (ν : ℝ) : Prop :=
  ∃ (u0 : E3 → E3) (f : ℝ → E3 → E3), AdmissibleInitialDatum u0 ∧ AdmissibleForcing f ∧
    ¬ ∃ (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ), IsNSSolution ν f u0 u p

/-! ## Calculus helpers -/

@[simp] lemma pd_const {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (j : Fin 3) (c : F) :
    pd j (fun _ : E3 => c) = fun _ => 0 := by
  funext x; simp [pd]

lemma pd_comp_coord (g : ℝ → ℝ) (i j : Fin 3) (x : E3) (hg : DifferentiableAt ℝ g (x i)) :
    pd j (fun y : E3 => g (y i)) x = if j = i then deriv g (x i) else 0 := by
  have h : HasFDerivAt (fun y : E3 => g (y i))
      (deriv g (x i) • (EuclideanSpace.proj i : E3 →L[ℝ] ℝ)) x :=
    hg.hasDerivAt.comp_hasFDerivAt x (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).hasFDerivAt
  unfold pd
  rw [h.fderiv]
  by_cases hji : j = i <;> simp [hji]

lemma pd_scale (j : Fin 3) (c c' : ℝ) (g : E3 → ℝ) :
    pd j (fun y : E3 => c * g (c' • y)) = fun x => c * c' * pd j g (c' • x) := by
  funext x
  unfold pd
  have h1 : (fun y : E3 => c * g (c' • y)) = c • (fun y : E3 => g (c' • y)) := by
    funext y; simp
  rw [h1, fderiv_const_smul_field, Pi.smul_apply, fderiv_comp_smul c']
  simp [mul_assoc]

/-! ## Sanity: zero solution -/

theorem zero_isNSSolution (ν : ℝ) :
    IsNSSolution ν (fun _ _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) where
  momentum := by
    intro t _ x i
    simp [dt, lap]
  incompressible := by
    intro t _ x
    simp [div]
  smooth_u := contDiffOn_const
  smooth_p := contDiffOn_const
  initial := fun _ => rfl
  bounded_energy := ⟨1, fun t _ => by simp⟩

lemma admissibleForcing_zero : AdmissibleForcing (fun _ _ => 0) := by
  refine ⟨contDiffOn_const, fun n K => ⟨0, fun z _ => ?_⟩⟩
  have : (fun _ : ℝ × E3 => (0 : E3)) = 0 := rfl
  simp [this]

theorem statementC_of_not_statementA (ν : ℝ) (h : ¬ StatementA ν) : StatementC ν := by
  unfold StatementA at h
  push Not at h
  obtain ⟨u0, hu0, hno⟩ := h
  exact ⟨u0, fun _ _ => 0, hu0, admissibleForcing_zero, fun ⟨u, p, hup⟩ => hno u p hup⟩

/-! ## Shear flows -/

/-- shear flow with profile `F t y`: velocity `(F(t, x₁), 0, 0)`. -/
noncomputable def shear (F : ℝ → ℝ → ℝ) (t : ℝ) (x : E3) : E3 :=
  EuclideanSpace.single (0 : Fin 3) (F t (x 1))

theorem shear_satisfiesNSEquations (ν : ℝ) (F : ℝ → ℝ → ℝ)
    (h1 : ∀ t, Differentiable ℝ (F t)) (h2 : ∀ t, Differentiable ℝ (deriv (F t)))
    (heat : ∀ t : ℝ, 0 ≤ t → ∀ y : ℝ,
      derivWithin (fun s => F s y) (Ici 0) t = ν * deriv (deriv (F t)) y) :
    SatisfiesNSEquations ν (fun _ _ => 0) (shear F) (fun _ _ => 0) where
  momentum := by
    intro t ht x i
    have hpd : ∀ j : Fin 3, pd j (fun y : E3 => F t (y 1))
        = fun y => if j = 1 then deriv (F t) (y 1) else 0 := by
      intro j; funext y; exact pd_comp_coord (F t) 1 j y (h1 t _)
    have hpd2 : ∀ j : Fin 3, pd j (fun y : E3 => deriv (F t) (y 1)) x
        = if j = 1 then deriv (deriv (F t)) (x 1) else 0 := by
      intro j; exact pd_comp_coord (deriv (F t)) 1 j x (h2 t _)
    fin_cases i
    · simp [shear, dt, lap, hpd, Fin.sum_univ_three, hpd2, heat t ht]
    · simp [shear, dt, lap]
    · simp [shear, dt, lap]
  incompressible := by
    intro t ht x
    have hpd : ∀ j : Fin 3, pd j (fun y : E3 => F t (y 1))
        = fun y => if j = 1 then deriv (F t) (y 1) else 0 := by
      intro j; funext y; exact pd_comp_coord (F t) 1 j y (h1 t _)
    simp [div, shear, Fin.sum_univ_three, hpd]

/-! ## Explicit sine shear -/

noncomputable def sinProfile (ν k : ℝ) (t y : ℝ) : ℝ :=
  Real.exp (-(ν * k ^ 2 * t)) * Real.sin (k * y)

lemma deriv_sinProfile (ν k t : ℝ) :
    deriv (sinProfile ν k t) = fun y => Real.exp (-(ν * k ^ 2 * t)) * (Real.cos (k * y) * k) := by
  funext y
  have h : HasDerivAt (fun y : ℝ => k * y) k y := by
    simpa using (hasDerivAt_id y).const_mul k
  exact (h.sin.const_mul _).deriv

lemma deriv_deriv_sinProfile (ν k t y : ℝ) :
    deriv (deriv (sinProfile ν k t)) y
      = Real.exp (-(ν * k ^ 2 * t)) * (-Real.sin (k * y) * k * k) := by
  rw [deriv_sinProfile]
  have h : HasDerivAt (fun y : ℝ => k * y) k y := by
    simpa using (hasDerivAt_id y).const_mul k
  exact ((h.cos.mul_const k).const_mul _).deriv

theorem sinShear_isSmoothNSSolution (ν k : ℝ) :
    IsSmoothNSSolution ν (fun _ _ => 0)
      (fun x : E3 => EuclideanSpace.single (0 : Fin 3) (Real.sin (k * x 1)))
      (shear (sinProfile ν k)) (fun _ _ => 0) where
  toSatisfiesNSEquations := by
    refine shear_satisfiesNSEquations ν _ ?_ ?_ ?_
    · intro t; unfold sinProfile; fun_prop
    · intro t; rw [deriv_sinProfile]; fun_prop
    · intro t ht y
      rw [deriv_deriv_sinProfile]
      have h : HasDerivAt (fun s : ℝ => -(ν * k ^ 2 * s)) (-(ν * k ^ 2)) t := by
        have h0 : HasDerivAt (fun s : ℝ => -(ν * k ^ 2 * s)) (-(ν * k ^ 2 * 1)) t :=
          ((hasDerivAt_id t).const_mul (ν * k ^ 2)).neg
        simpa using h0
      have h' := (h.exp.mul_const (Real.sin (k * y))).hasDerivWithinAt (s := Ici 0)
      unfold sinProfile
      rw [h'.derivWithin (uniqueDiffOn_Ici 0 t ht)]
      ring
  smooth_u := by
    apply ContDiff.contDiffOn
    rw [contDiff_euclidean]
    have hc : ContDiff ℝ ∞ (fun z : ℝ × E3 => z.2 1) :=
      (EuclideanSpace.proj (1 : Fin 3) : E3 →L[ℝ] ℝ).contDiff.comp contDiff_snd
    intro i
    fin_cases i
    · simp only [shear, sinProfile]
      simp
      fun_prop
    · simp [shear, contDiff_const]
    · simp [shear, contDiff_const]
  smooth_p := contDiffOn_const
  initial := by
    intro x
    simp [shear, sinProfile]

/-! ## Symmetries -/

theorem pressure_gauge {ν : ℝ} {f u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ} (c : ℝ → ℝ)
    (h : SatisfiesNSEquations ν f u p) :
    SatisfiesNSEquations ν f u (fun t x => p t x + c t) where
  momentum := by
    intro t ht x i
    have : pd i (fun x => p t x + c t) x = pd i (p t) x := by
      simp [pd]
    rw [this]
    exact h.momentum t ht x i
  incompressible := h.incompressible

noncomputable def scaleU (lam : ℝ) (u : ℝ → E3 → E3) (t : ℝ) (x : E3) : E3 :=
  lam • u (lam ^ 2 * t) (lam • x)

noncomputable def scaleP (lam : ℝ) (p : ℝ → E3 → ℝ) (t : ℝ) (x : E3) : ℝ :=
  lam ^ 2 * p (lam ^ 2 * t) (lam • x)

noncomputable def scaleF (lam : ℝ) (f : ℝ → E3 → E3) (t : ℝ) (x : E3) : E3 :=
  lam ^ 3 • f (lam ^ 2 * t) (lam • x)

theorem scaling_satisfiesNSEquations {ν lam : ℝ} {f u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (hlam : 0 < lam) (h : SatisfiesNSEquations ν f u p) :
    SatisfiesNSEquations ν (scaleF lam f) (scaleU lam u) (scaleP lam p) := by
  have hpd : ∀ (t : ℝ) (j k : Fin 3), pd j (fun y => scaleU lam u t y k)
      = fun y => lam * lam * pd j (fun y => u (lam ^ 2 * t) y k) (lam • y) := by
    intro t j k
    exact pd_scale j lam lam (fun y => u (lam ^ 2 * t) y k)
  constructor
  · intro t ht x i
    have hT : 0 ≤ lam ^ 2 * t := by positivity
    have key := h.momentum (lam ^ 2 * t) hT (lam • x) i
    have hdt : dt (fun s => scaleU lam u s x i) t
        = lam ^ 3 * dt (fun s => u s (lam • x) i) (lam ^ 2 * t) := by
      unfold dt scaleU
      simp only [PiLp.smul_apply, smul_eq_mul]
      rw [derivWithin_const_mul_field,
        derivWithin_comp_mul_left (lam ^ 2) (fun s => u s (lam • x) i) (Ici 0) t,
        LinearOrderedField.smul_Ici (by positivity)]
      simp only [smul_eq_mul, mul_zero]
      ring
    have hlap : lap (fun y => scaleU lam u t y i) x
        = lam ^ 3 * lap (fun y => u (lam ^ 2 * t) y i) (lam • x) := by
      unfold lap
      simp only [hpd, pd_scale, Fin.sum_univ_three]
      ring
    have hp : pd i (scaleP lam p t) x = lam ^ 3 * pd i (p (lam ^ 2 * t)) (lam • x) := by
      have e : scaleP lam p t = fun y => lam ^ 2 * p (lam ^ 2 * t) (lam • y) := rfl
      rw [e, pd_scale]; ring
    rw [hdt, hlap, hp]
    simp only [hpd, Fin.sum_univ_three] at key ⊢
    simp only [scaleU, scaleF, PiLp.smul_apply, smul_eq_mul]
    linear_combination lam ^ 3 * key
  · intro t ht x
    have hT : 0 ≤ lam ^ 2 * t := by positivity
    have key := h.incompressible (lam ^ 2 * t) hT (lam • x)
    simp only [div, hpd, Fin.sum_univ_three] at key ⊢
    linear_combination lam * lam * key

theorem scaling_isSmoothNSSolution {ν lam : ℝ} {f u : ℝ → E3 → E3} {u0 : E3 → E3}
    {p : ℝ → E3 → ℝ} (hlam : 0 < lam) (h : IsSmoothNSSolution ν f u0 u p) :
    IsSmoothNSSolution ν (scaleF lam f) (fun x => lam • u0 (lam • x))
      (scaleU lam u) (scaleP lam p) where
  toSatisfiesNSEquations := scaling_satisfiesNSEquations hlam h.toSatisfiesNSEquations
  smooth_u := by
    have hg : ContDiff ℝ ∞ (fun z : ℝ × E3 => (lam ^ 2 * z.1, lam • z.2)) := by fun_prop
    have hm : MapsTo (fun z : ℝ × E3 => (lam ^ 2 * z.1, lam • z.2)) spaceTime spaceTime := by
      rintro ⟨t, x⟩ ⟨ht, -⟩
      exact ⟨by simp only [mem_Ici] at ht ⊢; positivity, mem_univ _⟩
    exact (h.smooth_u.comp hg.contDiffOn hm).const_smul lam
  smooth_p := by
    have hg : ContDiff ℝ ∞ (fun z : ℝ × E3 => (lam ^ 2 * z.1, lam • z.2)) := by fun_prop
    have hm : MapsTo (fun z : ℝ × E3 => (lam ^ 2 * z.1, lam • z.2)) spaceTime spaceTime := by
      rintro ⟨t, x⟩ ⟨ht, -⟩
      exact ⟨by simp only [mem_Ici] at ht ⊢; positivity, mem_univ _⟩
    exact (h.smooth_p.comp hg.contDiffOn hm).const_smul (lam ^ 2)
  initial := by
    intro x
    simp [scaleU, h.initial]

end NavierStokes

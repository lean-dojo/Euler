module

public import Review.Definitions

/-!
# Reference statements for Comparator

The paper is https://arxiv.org/abs/2609.10867.
The eight deliberate placeholders specify claims to check; they are not proofs.
The submitted proofs come from Euler, which never imports this module.
-/

@[expose] public noncomputable section

open Euler Euler.Calculus Euler.Coordinates Euler.Similarity Euler.Axisymmetric
open Euler.Cartesian Euler.Stability Euler.Linearization Euler.PhysicalTime
open MeasureTheory Set Filter
open scoped Topology ENNReal
local notation "Dz" => partialDeriv (1 : Fin 2)

namespace Euler

/-- A/C: similarity profiles and physical equations. -/
theorem isConvectionVariedSolutionOn_similarityFields_iff
    (eps : ℝ) (F : Profile)
    (lam axialDrift singularTime : ℝ) (axialCenter : ℝ → ℝ)
    (Ωdom : Set (ℝ^2)) (I : Set ℝ)
    (hU : ∀ x ∈ Ωdom, ∀ t ∈ I, DifferentiableAt ℝ F.U
      (similarityCoordinates lam singularTime axialCenter x t))
    (hOmega : ∀ x ∈ Ωdom, ∀ t ∈ I, DifferentiableAt ℝ F.Ω
      (similarityCoordinates lam singularTime axialCenter x t))
    (hPsi : ContDiff ℝ 2 F.Ψ)
    (hcenter : ∀ t ∈ I, HasDerivAt axialCenter
      (-axialDrift * backwardPowerScale (1 - lam) singularTime t) t)
    (htime : ∀ t ∈ I, t < singularTime) :
    (similarityFields F lam singularTime axialCenter).IsConvectionVariedSolutionOn
        eps Ωdom I ↔
      F.IsStationaryOn eps lam axialDrift
        classicalAxisymmetricDifferential
        (travelingProfileDomain lam singularTime axialCenter Ωdom I) := by
  sorry

end Euler

namespace Euler.Coordinates

/-- B: elliptic operator in sinh coordinates. -/
theorem computationalElliptic_sinhPullback {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 2 f) (x : (ℝ^2)) :
    computationalElliptic (sinhPullback f) x =
      axisymmetricLaplacian classicalAxisymmetricDifferential f
        (sinhCoordinates x) := by
  sorry

end Euler.Coordinates

namespace Euler.Axisymmetric

/-- D: dynamic rescaling and the rate identity. -/
theorem satisfiesRescaledEquationsOn_of_scale_compatibility
    (eps : ℝ) (data : Rescaling) (fields : ReducedFields)
    (physicalDomain rescaledDomain : Set (ℝ^2))
    (physicalTimes rescaledTimes : Set ℝ)
    (hphysical :
      SatisfiesPhysicalEquationsOn eps fields physicalDomain physicalTimes)
    (hdomain : rescaledDomain ⊆ positiveRadiusMeridian)
    (hmap :
      ∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄, x ∈ rescaledDomain → τ ∈ rescaledTimes →
        rescalingMap data x τ ∈ physicalDomain ∧
          data.physicalTime τ ∈ physicalTimes)
    (hswirl_pos :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes → 0 < data.swirlScale τ)
    (hspatial_pos :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes → 0 < data.spatialScale τ)
    (hswirlScale :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt data.swirlScale (data.swirlRate τ * data.swirlScale τ) τ)
    (hspatialScale :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt data.spatialScale (-data.spatialRate τ * data.spatialScale τ) τ)
    (hvorticityScale :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt data.vorticityScale (data.vorticityRate τ * data.vorticityScale τ) τ)
    (hcenter :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt (fun s ↦ data.axialCenter s • axialUnit)
          ((-data.axialDrift τ * data.spatialScale τ) • axialUnit) τ)
    (hclock :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt data.physicalTime (data.swirlScale τ) τ)
    (hcompat :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        data.vorticityScale =ᶠ[𝓝 τ] fun s ↦ data.swirlScale s * data.spatialScale s)
    (hswirl :
      ∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄, x ∈ rescaledDomain → τ ∈ rescaledTimes →
        DifferentiableAt ℝ (Function.uncurry fields.swirl)
          (rescalingMap data x τ, data.physicalTime τ))
    (hvorticity :
      ∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄, x ∈ rescaledDomain → τ ∈ rescaledTimes →
        DifferentiableAt ℝ (Function.uncurry fields.vorticity)
          (rescalingMap data x τ, data.physicalTime τ))
    (hstream :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        ContDiff ℝ 2 (fun y ↦ fields.streamFunction y (data.physicalTime τ))) :
    SatisfiesRescaledEquationsOn eps
        (rescaledFields data fields)
        data.spatialRate data.axialDrift data.swirlRate data.vorticityRate
        rescaledDomain rescaledTimes ∧
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        data.vorticityRate τ = data.swirlRate τ - data.spatialRate τ := by
  sorry

end Euler.Axisymmetric

namespace Euler

/-- E: physical energy scaling. -/
theorem physicalEnergy_similarity
    (eps : ℝ) (U Ψ : ℝ^2 → ℝ) (lam singularTime : ℝ) (axialCenter : ℝ → ℝ) {t : ℝ}
    (hΨ : ∀ q : PositiveMeridian, DifferentiableAt ℝ Ψ
      (similarityCoordinates lam singularTime axialCenter (positiveMeridianPoint q) t))
    (hintegrable : Integrable
      (fun q : PositiveMeridian ↦ profileEnergyDensity eps U Ψ (positiveMeridianPoint q))
      weightedMeridianMeasure)
    (ht : t < singularTime) :
    physicalEnergy eps (similarityScalar U 1 lam singularTime axialCenter)
        (similarityScalar Ψ (1 - lam) lam singularTime axialCenter) t =
      (singularTime - t) ^ (5 * lam - 2) * profileEnergy eps U Ψ := by
  sorry

end Euler

namespace Euler.Cartesian

/-- F: Euler scaling symmetry. -/
theorem scaling_preserves_equations
    {η α : ℝ} (hη : 0 < η) (u : VectorField) (p : ScalarField) (I : Set ℝ)
    (ht : ∀ x t, t ∈ I → ∀ i, DifferentiableAt ℝ (fun s ↦ u x s i) t)
    (hx : ∀ x t, t ∈ I → ∀ i, DifferentiableAt ℝ (fun y ↦ u y t i) x)
    (hp : ∀ x t, t ∈ I → DifferentiableAt ℝ (fun y ↦ p y t) x)
    (heuler : ∀ x t, t ∈ I →
      momentumResidual u p x t = 0 ∧ divergence u x t = 0) :
    ∀ x t, t ∈ scaledTimeSet η α I →
      momentumResidual (scaledVelocity η α u) (scaledPressure η α p) x t = 0 ∧
        divergence (scaledVelocity η α u) x t = 0 := by
  sorry

end Euler.Cartesian

namespace Euler.Linearization

/-- G: amplitude modulation from normalization. -/
theorem amplitude_modulation (lam C cu dC dcu : ℝ)
    (u psi : ℝ^2 → ℝ) (du dp : ℝ^2 → ℝ → ℝ) (t : ℝ)
    (hu : u 0 ≠ 0)
    (href : C + 2 * psi 0 = 0)
    (hfull : C + dC + 2 * (psi 0 + dp 0 t) = 0)
    (htrace : ∀ s, u 0 + du 0 s = u 0)
    (hp : DifferentiableAt ℝ psi 0)
    (hdp : DifferentiableAt ℝ (fun y ↦ dp y t) 0)
    (heq : deriv (fun s ↦ u 0 + du 0 s) t =
      swirlEvolution lam (C + dC)
        (cu + amplitudeOffset u (swirlEvolution lam C cu u psi) + dcu)
        (fun y ↦ u y + du y t) (fun y ↦ psi y + dp y t) 0) :
    dcu = -2 * Dz (fun y ↦ dp y t) 0 := by
  sorry

end Euler.Linearization

namespace Euler.Stability

/-- I: conditional energy stability. -/
theorem energy_lt_of_initial_lt {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {k : ℕ} {c : EnergyConstants} {μ δ a : ℝ} {s : Set ℝ}
    {low : EnergyComponents (Fin 3) V} {high : EnergyComponents (MixedDerivativeIndex k) V}
    (hs : OrdConnected s) (ha : a ∈ s)
    (hlow : low.EvolvesOn s) (hhigh : high.EvolvesOn s)
    (hbound : ∀ t ∈ s, energy μ low high t ≤ δ → PairingBounds c μ low high t)
    (hμ : μ ∈ Ioc (0 : ℝ) 1) (_hdamping : 0 < c.damping μ) (hδ : 0 < δ)
    (hmargin : c.cubic * δ + c.residual / δ < c.damping μ)
    (hinitial : energy μ low high a < δ) :
    ∀ t ∈ s, a ≤ t → energy μ low high t < δ := by
  sorry

end Euler.Stability

namespace Euler

/-- J: conditional physical-time reconstruction. -/
theorem physical_reconstruction_estimates
    (a b w : ScalarField) (sU cU center C : ℝ → ℝ)
    (barU gamma sr₀ lam K : ℝ)
    (hgamma : 0 < gamma) (hsU0 : 0 < sU 0) (hbarU : barU ≠ 0)
    (hscale : ∀ τ ∈ Ici (0 : ℝ), HasDerivAt sU (-cU τ * sU τ) τ)
    (hrate : ∀ τ ∈ Ici (0 : ℝ), cU τ ≤ -gamma)
    (hsr : 0 ≤ sr₀) (hlam : 0 < lam)
    (hC : ContinuousOn C (Ici (0 : ℝ)))
    (hCbound : ∀ τ ∈ Ici (0 : ℝ), |C τ| ≤ K)
    (hcenter : ∀ τ ∈ Ici (0 : ℝ),
      HasDerivAt center (travelingCenterVelocity C sr₀ lam τ) τ)
    (ha : ∀ τ ∈ Ici (0 : ℝ),
      DifferentiableAt ℝ
        (fun x ↦ a x (∫ s in (0 : ℝ)..τ, (sU s)⁻¹)) (axisPoint (center τ)))
    (hb : ∀ τ ∈ Ici (0 : ℝ),
      DifferentiableAt ℝ
        (fun x ↦ b x (∫ s in (0 : ℝ)..τ, (sU s)⁻¹)) (axisPoint (center τ)))
    (hnormalize : ∀ τ ∈ Ici (0 : ℝ),
      b (axisPoint (center τ)) (∫ s in (0 : ℝ)..τ, (sU s)⁻¹) = sU τ * barU)
    (hcurl : ∀ τ ∈ Ici (0 : ℝ), Continuous
      (fun x ↦ curl (axisymmetricVelocity a b w)
        x (∫ s in (0 : ℝ)..τ, (sU s)⁻¹))) :
    let clock := fun τ ↦ ∫ s in (0 : ℝ)..τ, (sU s)⁻¹
    let T := ∫ s in Ioi (0 : ℝ), (sU s)⁻¹
    let zStar := center 0 + ∫ τ in Ioi (0 : ℝ), travelingCenterVelocity C sr₀ lam τ
    IntegrableOn (fun τ ↦ (sU τ)⁻¹) (Ioi (0 : ℝ)) ∧
      (∀ τ ∈ Ici (0 : ℝ),
        0 < T - clock τ ∧ T - clock τ ≤ (sU 0)⁻¹ * Real.exp (-gamma * τ) / gamma) ∧
      StrictMonoOn clock (Ici (0 : ℝ)) ∧
      clock '' Ici (0 : ℝ) = Ico 0 T ∧
      Tendsto clock atTop (𝓝 T) ∧
      Tendsto center atTop (𝓝 zStar) ∧
      Tendsto (fun τ ↦ |curl (axisymmetricVelocity a b w)
        (axisPoint (center τ)) (clock τ) 2|) atTop atTop ∧
      Tendsto (fun τ ↦ eLpNorm
        (fun x ↦ curl (axisymmetricVelocity a b w) x (clock τ))
        (⊤ : ℝ≥0∞) volume) atTop (𝓝 (⊤ : ℝ≥0∞)) ∧
      ¬∃ extension : ℝ × ℝ → ℝ,
        (∀ᶠ p in 𝓝 (zStar, T), p.2 < T →
          extension p = curl (axisymmetricVelocity a b w)
            (axisPoint p.1) p.2 2) ∧
        ContinuousAt extension (zStar, T) := by
  sorry

end Euler

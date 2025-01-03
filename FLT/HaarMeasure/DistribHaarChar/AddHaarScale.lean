/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.HaarMeasure.DomMulActMeasure
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib
/-!
# Scaling Haar measures by automorphisms.

Given a locally compact commutative group, it has a regular Haar measure,
unique up to scaling. An automorphism of this group scales this Haar measure
by a positive real factor independent of the choice of measure.

-/

-- for mathlib. Also change docstring of `MeasureTheory.Measure.isHaarMeasure_map`
-- to mention it and also `ContinuousLinearEquiv.isAddHaarMeasure_map` in the
-- additive case
/--
A convenience wrapper for MeasureTheory.Measure.isHaarMeasure_map.
-/
@[to_additive "A convenience wrapper for MeasureTheory.Measure.isAddHaarMeasure_map.
"]
lemma ContinuousMulEquiv.isHaarMeasure_map {G : Type*} [MeasurableSpace G] [Group G]
    [TopologicalSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] [BorelSpace G]
    [TopologicalGroup G] {H : Type*} [Group H] [TopologicalSpace H] [MeasurableSpace H]
    [BorelSpace H] [TopologicalGroup H] (e : G ≃ₜ* H) :
    (MeasureTheory.Measure.map (⇑e) μ).IsHaarMeasure :=
  e.toMulEquiv.isHaarMeasure_map μ e.continuous e.symm.continuous

namespace MeasureTheory.Measure

variable {A : Type*} [TopologicalSpace A] [LocallyCompactSpace A]
  [MeasurableSpace A] [BorelSpace A]
  [CommGroup A] [TopologicalGroup A]

@[to_additive]
instance (φ : A ≃ₜ* A) (μ : Measure A) [Regular μ] : Regular (μ.map φ) :=
  Regular.map φ.toHomeomorph

@[to_additive]
instance (φ : A ≃ₜ* A) (μ : Measure A) [IsHaarMeasure μ] : IsHaarMeasure (μ.map φ) :=
  φ.isHaarMeasure_map μ

open scoped NNReal
/-- If `A` is a locally compact topological abelian multiplicative group and
`φ : A ≃ₜ* A` then `haarScale φ` is the positive real number
such that `μ (φ s) = (haarScale φ) * μ s` for sensible `s`.
-/
@[to_additive "If `A` is a locally compact topological abelian additive group and
`φ : A ≃ₜ+ A` then `addHaarScale φ` is the positive real number
such that `μ (φ s) = (addHaarScale φ) * μ s` for sensible `s`."]
noncomputable def haarScale (φ : A ≃ₜ* A) : ℝ≥0 :=
  haarScalarFactor haar (haar.map φ)

/-
noncomputable def φ : ℝ ≃ₜ+ ℝ where
  toFun x := 2 * x
  invFun y := y / 2
  left_inv x := by simp
  right_inv y := by simp; ring
  map_add' x₁ x₂ := by simp; ring

example : addHaarScale φ = 2 := by
  unfold addHaarScale
  have := measure_isAddInvariant_eq_smul_of_isCompact_closure addHaar (map (⇑φ) addHaar) (s := Set.Icc 0 1) sorry
  have foo : AEMeasurable (⇑φ) addHaar := sorry
  have bar : NullMeasurableSet (Set.Icc 0 1) (map (⇑φ) addHaar) := sorry
  rw [map_apply₀ foo bar] at this; clear foo; clear bar
  have foo2 : φ ⁻¹' Set.Icc 0 1 =  Set.Icc 0 (1/2) := by
    ext x
    simp only [φ, ContinuousAddEquiv.coe_mk, AddEquiv.coe_mk, Equiv.coe_fn_mk, Nat.ofNat_pos,
      Set.preimage_const_mul_Icc, zero_div, one_div, Set.mem_Icc]
  rw [foo2] at this; clear foo2
  rw [show addHaar (Set.Icc (0 : ℝ) 1) = 2 * addHaar (Set.Icc (0 : ℝ) (1/2)) by sorry] at this
  simp at this
  sorry -- looks good to me, normalization the right way around
-/

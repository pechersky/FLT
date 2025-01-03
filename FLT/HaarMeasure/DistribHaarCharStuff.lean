import FLT.HaarMeasure.DistribHaarChar.Basic

namespace MeasureTheory.Measure

open scoped NNReal

variable (R : Type*) [TopologicalSpace R] [LocallyCompactSpace R]
  [CommRing R] [TopologicalRing R]
  [MeasurableSpace R] [BorelSpace R]

theorem distribHaarChar_continuous : Continuous (distribHaarChar R : Rˣ →* ℝ≥0) := by
  sorry -- is this true?

variable {S : Type*} [TopologicalSpace S] [LocallyCompactSpace S]
  [CommRing S] [TopologicalRing S]
  [MeasurableSpace S] [BorelSpace S]

/-
This theorem below is true even if neither R or S is second countable,
but without these assumptions it is difficult to *state* in Lean,
because typeclass inference gives `R × S` the product topology and
the product sigma algebra, but unfortunately the product of two
Borel sigma algebras is not the Borel sigma algebra without the
countability assumption, meaning that one has to fight the typeclass
system to talk about Haar measure on the product. See
https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Product.20of.20Borel.20spaces/near/487237491

Under the assumption `[SecondCountableTopologyEither R S]` we have
`Prod.borelSpace : BorelSpace (R × S)` and so we don't need to fight
the typeclass system to state the result.
-/
theorem distribHaarChar_prod_apply [SecondCountableTopologyEither R S] (r : Rˣ) (s : Sˣ) :
    distribHaarChar (R × S) (MulEquiv.prodUnits.symm (r, s)) =
      (distribHaarChar R r) * distribHaarChar S s := by
  sorry

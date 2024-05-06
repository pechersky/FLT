import Mathlib.RingTheory.HopfAlgebra
import Mathlib.AlgebraicGeometry.Spec

-- For now, let's model an affine group scheme over a field as a Hopf algebra

universe u

-- let K be a field
variable (K : Type u) [Field K]

-- Let G be an affine algebraic group over K, modelled as G=Spec(H) for H a
-- Hopf algebra
variable (H : Type u) [CommRing H] [HopfAlgebra K H]

open AlgebraicGeometry

-- We can say "assume G is connected":

namespace HopfAlgebra

abbrev IsConnected (K : Type u) [Field K] (H : Type u) [CommRing H] [HopfAlgebra K H] : Prop :=
  ConnectedSpace (Spec.topObj (CommRingCat.of H))

-- But reductive is more work. Let's sorry the definition for now.
def IsReductive_def (K : Type u) [Field K] (H : Type u) [CommRing H] [HopfAlgebra K H] : Prop := sorry

/-- A Hopf algebra over a field `K` is *reductive* if the associated group scheme
is reductive. -/class IsReductive (K : Type u) [Field K] (H : Type u) [CommRing H] [HopfAlgebra K H] : Prop where
  isReductive : IsReductive_def K H

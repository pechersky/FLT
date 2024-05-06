import FLT.GroupScheme.ConnectedReductive
import Mathlib.NumberTheory.NumberField.Basic

-- let K be a field and let G be a connected reductive group scheme over K
-- which we internally represent as a Hopf algebra

universe u

open HopfAlgebra

/-

Right now we are very far from being able to make the definition of an automorphic representation.

The main issues:

1) We need to define what is means for `Spec(H)` to be a connected reductive group
over `Spec(K)`, if `H` is a Hopf algebra over a field `K`. This probably involves
making a definition of a unipotent subgroup of a group variety over `K`.

2) If `G` is a connected reductive group over the reals (e.g. GL_n/ℝ or a symplectic
or orthogonal group, or E_8 or the units in the quaternions or whatever), then we
need

2a) a Lie group structure on `G(ℝ)` (plus proof that the manifold structure on `G(ℝ)`
is "canonical", i.e. independent of any choice of embedding into `ℝⁿ`)
2b) The Lie algebra 𝓛 of this Lie group (or more generally of any Lie group)
2c) An action of 𝓛 and also its universal enveloping algebra on the C^∞ functions on G(ℝ).

This is not high priority right now, because we will be able to make progress
with an ad hoc definition valid only for the unit groups of totally definite
quaternion algebras.
-/

def AutomorphicRepresentation (K : Type u) [Field K] [NumberField K]
    (H : Type u) [CommRing H] [HopfAlgebra K H]
    [IsConnected K H] [IsReductive K H] : Type u := sorry

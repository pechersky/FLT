import Mathlib.AlgebraicGeometry.EllipticCurve.Group
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RepresentationTheory.Basic
import Mathlib.Data.Set.Card

/-

# Mazur's theorem

A statement of Mazur's torsion theorem.

-/

open WeierstrassCurve

theorem Mazur (E : EllipticCurve ℚ) :
    {P : E.toWeierstrassCurve ⟮ℚ⟯ | ∃ n ≥ 1, n • P = 0}.ncard ≤ 16 := sorry
